(* TODO: 
 * - rename nat => int
 * - operations on int (+,*,/,print)
 * - remove succ
 * - list-type
 *)
open Term
open Compile

let fresh_var = Vargen.mkVarGenerator "x" ~avoid:[]
let context = Llvm.global_context ()
let builder = Llvm.builder context

(* Encapsulate bit vectors to make it easy to change the llvm-encoding. *)
module Bitvector :
sig 
  type t
  val length : t -> int
  val undef : int -> t
  val null : int -> t
  val concat : t -> t -> t
  val takedrop : int -> t -> t * t
  val extractvalue : t -> int -> Llvm.llvalue
  val of_list: Llvm.llvalue list -> t

  val build_phi: (t * Llvm.llbasicblock) list -> Llvm.llbuilder -> t
  val add_incoming: t * Llvm.llbasicblock -> t -> unit
end = 
struct
  type t = { bits : Llvm.llvalue list }

  let i1 = Llvm.i1_type context

  let length b = List.length b.bits

  let null len = { bits = Listutil.init len (fun _ -> Llvm.const_null i1) }

  let undef len = { bits = Listutil.init len (fun _ -> Llvm.undef i1) }

  let concat b1 b2 = { bits = b1.bits @ b2.bits }

  let takedrop n b1 = 
    let l1, l2 = Listutil.part n b1.bits in
      { bits = l1 }, { bits = l2 }

  let extractvalue b i =
    match Listutil.part i b.bits with
      | _, x :: _ -> x
      | _, [] -> assert false

  let of_list bl = { bits = bl }

  let rec transpose l =
         let rec split_list heads tails l =
           match l with
             | [] -> List.rev heads, List.rev tails
             | [] :: _ -> assert false
             | (h :: t) :: l' -> split_list (h :: heads) (t :: tails) l' 
         in
           match l with
             | [] | [] :: _ -> []
             | _ -> 
                 let heads, tails = split_list [] [] l in
                   heads :: transpose tails 

  let build_phi srcs builder =
    let l = List.map (fun (x,src) -> List.map (fun xi -> (xi, src)) x.bits) srcs in
    let l' = transpose l in
      { bits = List.map (fun isrcs -> Llvm.build_phi isrcs "z" builder) l' }

  let add_incoming (y, blocky) x =
    List.iter 
      (fun (yi, xi) -> Llvm.add_incoming (yi, blocky) xi)
      (List.combine y.bits x.bits)
end

type encoded_value = {
  payload : Llvm.llvalue list;
  attrib: Bitvector.t
}
  
let position_at_start block builder =
  let block_begin = Llvm.instr_begin block in
    Llvm.position_builder block_begin builder

 (*
 * Payload:
 *   <> -> []
 *   <t1,t2> -> (payload t1) @ (payload t2)
 *   inl(t1) -> (payload t1)
 *   inr(t2) -> (payload t2)
 *
 * Attribution:
 *   <> -> []
 *   <t1,t2> -> (attrib t1) | (attrib t2)
 *   inl(t1) -> (attrib t1) | 0
 *   inl(t1) -> (attrib t1) | 1
 *
 * Payload-Size:
 *   1 -> 0
 *   N -> 1
 *   A*B -> (payload_size A) + (payload_size B)
 *   A+B -> max(payload_size A, payload_size B)
 *
 * Attrib-Size:
 *   1 -> 0
 *   N -> 0
 *   A*B -> (attrib_size A) + (attrib_size B)
 *   A+B -> max(attrib_size A, attrib_size B)
 *)

(* 
 * Namensschema: 
 * Payload: x.0, x.1, ..., x.(payload_size -1)
 * Attrib: x.a
 *)

let rec payload_size (a: Type.t) : int = 
  let payload_size_memo = Type.Typetbl.create 5 in
  let rec p_s a = 
  try Type.Typetbl.find payload_size_memo a with
    | Not_found ->
        let size =
          let open Type in
            match finddesc a with
              | Link _ -> assert false
              | Var(_) | ZeroW | OneW -> 0
              | NatW -> 1
              | TensorW(a1, a2) -> p_s a1 + (p_s a2)
              | SumW[a1; a2] -> (max (p_s a1) (p_s a2))
              | MuW _ -> 1
              | FunW(_, _) | BoxU(_, _) | TensorU(_, _) | FunU(_, _, _) | SumW _ -> assert false
        in
          Type.Typetbl.add payload_size_memo a size;
          size
  in p_s a

let attrib_size (a: Type.t) : int =
  let attrib_size_memo = Type.Typetbl.create 5 in
  let rec a_s a = 
  try Type.Typetbl.find attrib_size_memo a with
    |Not_found ->
        let size =
          let open Type in
            match finddesc a with
              | Link _ -> assert false
              | Var | ZeroW | OneW | NatW -> 0
              | TensorW(a1, a2) -> a_s a1 + (a_s a2)
              | SumW[a1; a2] -> 1 + (max (a_s a1) (a_s a2))
              | MuW _ -> 0
              | FunW(_, _) | BoxU(_, _) | TensorU(_, _) | FunU(_, _, _) | SumW _ -> assert false
        in
          Type.Typetbl.add attrib_size_memo a size;
          size
  in a_s a
       

let build_concat 
      (v1 : Llvm.llvalue list) (l1 : int) 
      (v2 : Llvm.llvalue list) (l2 : int) : Llvm.llvalue list =
  v1 @ v2

let build_split (z : Llvm.llvalue list) (len1 : int) (len2 : int) 
      : Llvm.llvalue list * Llvm.llvalue list =
  Listutil.part len1 z

(* TODO: check that truncation is correctly applied! 
* *)                      
let build_truncate_extend (enc : encoded_value) (a : Type.t) =
  let a_payload_size = payload_size a in
  let a_attrib_bitlen = attrib_size a in
  let rec mk_payload p n =
    if n = 0 then [] else 
      match p with
        | [] -> Llvm.undef (Llvm.i64_type context) :: (mk_payload [] (n-1)) 
        | x::xs -> x :: (mk_payload xs (n-1)) in
  let x_payload = mk_payload enc.payload a_payload_size in
  let x_attrib = 
    let enc_attrib_bitlen = Bitvector.length enc.attrib in
      if enc_attrib_bitlen = a_attrib_bitlen then
        enc.attrib
      else if enc_attrib_bitlen < a_attrib_bitlen then
        (let leading_zeros = Bitvector.undef (a_attrib_bitlen - enc_attrib_bitlen) in
          Bitvector.concat leading_zeros enc.attrib)
      else (* enc_attrib_bitlen > a_attrib_bitlen *) 
        (let h, t = Bitvector.takedrop 
                      (enc_attrib_bitlen - a_attrib_bitlen) 
                      enc.attrib in
           t) in
    assert (Bitvector.length x_attrib = a_attrib_bitlen);
    { payload = x_payload; attrib = x_attrib }

(* TODO: 
 * - restrict wc so that this compilation is always ok. (remove functions)
 * - add loops
 * *)                      
let build_term 
      (the_module : Llvm.llmodule)
      (ctx: (var * encoded_value) list) 
      (type_ctx: (var * Type.t) list) (t: Term.t) (a: Type.t)
      : encoded_value =
  (* Add type annotations in various places *)
  let rec annotate_term (t: Term.t) : Term.t =
    match t.desc with
      | Var(_) | UnitW | ConstW(_) -> t
      | TypeAnnot(t1, None) -> annotate_term t1
      | TypeAnnot(t1, Some a) -> mkTypeAnnot (annotate_term t1) (Some a)
      | PairW(t1, t2) -> 
          let alpha = Type.newty Type.Var in
            mkTypeAnnot (mkPairW (annotate_term t1) (annotate_term t2)) (Some alpha)
      | LetW(t1, (x, y, t2)) ->
          let alpha = Type.newty Type.Var in
            mkLetW (mkTypeAnnot (annotate_term t1) (Some alpha)) ((x, y), annotate_term t2)
      | InW(2, 0, t1) -> 
          let alpha = Type.newty Type.Var in
            mkTypeAnnot (mkInlW (annotate_term t1)) (Some alpha)
      | InW(2, 1, t1) -> 
          let alpha = Type.newty Type.Var in
            mkTypeAnnot (mkInrW (annotate_term t1)) (Some alpha)
      | InW(_, _, _) -> assert false
      | CaseW(t1, [(x, t2); (y, t3)]) ->
          let alpha = Type.newty Type.Var in
              (mkCaseW 
                 (mkTypeAnnot (annotate_term t1) (Some alpha)) 
                 [(x, annotate_term t2); (y, annotate_term t3)])
      | CaseW(_, _) -> assert false
(*      | AppW({ desc=LetW(s, (x, y, t1)) }, t2) -> 
          let fvt2 = free_vars t2 in
          let x' = variant_var_avoid x fvt2 in
          let y' = variant_var_avoid y fvt2 in
          annotate_term (mkLetW s ((x', y'), mkAppW (subst (mkVar y') y (subst (mkVar x') x t1)) t2))*)
      | AppW(t1, t2) -> mkAppW (annotate_term t1) (annotate_term t2)
      | LambdaW((x, a), t1) -> mkLambdaW ((x, a), annotate_term t1)
      | LoopW(t1, (x, t2)) -> 
          let alpha = Type.newty Type.Var in
            mkLoopW (annotate_term t1) (x, mkTypeAnnot (annotate_term t2) (Some alpha))
      | FoldW((alpha, a), t1) -> mkFoldW (alpha, a) (annotate_term t1)
      | UnfoldW((alpha, a), t1) -> mkUnfoldW (alpha, a) (annotate_term t1)
      | LetBoxW(_, _) -> assert false 
      | HackU (_, _)|CopyU (_, _)|CaseU (_, _, _)|LetBoxU (_, _)
      | BoxTermU _| LambdaU (_, _)|AppU (_, _)|LetU (_, _)|PairU (_, _) -> assert false
  in
  (* Compile annotated term *)
  let rec build_annotatedterm 
        (ctx: (string * encoded_value) list) 
        (t: Term.t) 
        (args: encoded_value list)
        : encoded_value =
(*    print_string (Printing.string_of_termW t);
    print_string "\n";*)
    match t.Term.desc with
      | Var(x) -> 
          List.assoc x ctx
      | ConstW(Cintconst(i)) ->
          let vali = Llvm.const_int (Llvm.i64_type context) i in
            {payload = [vali]; attrib = Bitvector.null 0;}
      | ConstW(Cintprint) ->
          begin
            match List.hd args with
              | {payload = [x]; attrib = a} when Bitvector.length a = 0 -> 
                  let i8a = Llvm.pointer_type (Llvm.i8_type context) in
                  let i64 = Llvm.i64_type context in
                  let formatstr = Llvm.build_global_string "%i" "format" builder in            
                  let formatstrptr = Llvm.build_in_bounds_gep formatstr (Array.make 2 (Llvm.const_null i64)) "forrmatptr" builder in
                  let printftype = Llvm.function_type (Llvm.i64_type context) (Array.of_list [i8a; i64]) in
                  let printf = Llvm.declare_function "printf" printftype the_module in
                  let args = Array.of_list [formatstrptr; x] in
                    ignore (Llvm.build_call printf args "i" builder);
                    {payload = []; attrib = Bitvector.null 0 }
              | _ -> assert false
          end
      | ConstW(binop) when (binop = Cintadd || binop = Cintsub || 
                            binop = Cintmul || binop = Cintdiv) ->
          begin
            match args with
              | t1enc :: t2enc :: args' ->
                  begin
                    match t1enc, t2enc with
                      | {payload = [x]; attrib = ax },  {payload = [y]; attrib = ay } when   
                          Bitvector.length ax = 0  && Bitvector.length ay = 0 ->
                          let res =
                            match binop with
                              | Cintadd -> Llvm.build_add x y "add" builder 
                              | Cintsub -> Llvm.build_sub x y "sub" builder 
                              | Cintmul -> Llvm.build_mul x y "mul" builder 
                              | Cintdiv -> Llvm.build_sdiv x y "sdiv" builder 
                              | _ -> assert false
                          in
                            {payload = [res]; attrib = Bitvector.null 0}
                      | _ -> assert false
                  end
              | _ -> assert false
          end
      | ConstW(rel) when (rel = Cinteq || rel = Cintslt) ->
          begin
            match args with
              | t1enc :: t2enc :: args' ->
                  begin
                    match t1enc, t2enc with
                      | {payload = [x]; attrib = ax},  {payload = [y]; attrib = ay} when
                          Bitvector.length ax = 0  && Bitvector.length ay = 0 ->                          
                          let res = 
                            match rel with
                              | Cinteq -> Llvm.build_icmp Llvm.Icmp.Ne x y "eq" builder 
                              | Cintslt -> Llvm.build_icmp Llvm.Icmp.Sge x y "slt" builder 
                              | _ -> assert false
                          in
                            {payload = []; attrib = Bitvector.of_list [res]}
                      | _ -> assert false
                  end
              | _ -> assert false
          end
      | ConstW(Cprint(s)) ->
          let i64 = Llvm.i64_type context in
          let str = Llvm.build_global_string s "s" builder in            
          let strptr = Llvm.build_in_bounds_gep str (Array.make 2 (Llvm.const_null i64)) "strptr" builder in
            (* declare puts *)
          let i8a = Llvm.pointer_type (Llvm.i8_type context) in
          let putstype = Llvm.function_type (Llvm.i64_type context) (Array.make 1 i8a) in
          let puts = Llvm.declare_function "puts" putstype the_module in
          let args = Array.make 1 strptr in
            ignore (Llvm.build_call puts args "i" builder);
            {payload = []; attrib = Bitvector.null 0}
      | UnitW ->
          {payload = []; attrib = Bitvector.null 0}
      | TypeAnnot({ desc = PairW(t1, t2) }, Some a) ->
          assert (args = []);
          begin
            match Type.finddesc a with
              | Type.TensorW(a1, a2) ->
                  let t1enc = build_annotatedterm ctx t1 [] in
                  let t2enc = build_annotatedterm ctx t2 [] in
                  let ta = Bitvector.concat t1enc.attrib t2enc.attrib in
                    {payload = t1enc.payload @ t2enc.payload; attrib = ta}
              | _ -> assert false
          end
      | LetW({ desc = TypeAnnot(s, Some a) }, (x, y, t)) ->
          begin
            match Type.finddesc a with
              | Type.TensorW(ax, ay) ->
                  let senc = build_annotatedterm ctx s [] in
                  let len_sxp = payload_size ax in
                  let len_syp = payload_size ay in
                  let len_sxa = attrib_size ax in
                  let len_sya = attrib_size ay in
                    assert (List.length senc.payload = len_sxp + len_syp);
                    assert (Bitvector.length senc.attrib = len_sxa + len_sya);
                    let sxp, syp = Listutil.part len_sxp senc.payload in
                    let sxa, sya = Bitvector.takedrop len_sxa senc.attrib in
                      assert (Bitvector.length sya = len_sya);
                      build_annotatedterm ((x, {payload = sxp; attrib = sxa }) :: 
                                           (y, {payload = syp; attrib = sya }) :: ctx) t args
              | _ -> assert false
          end
      | TypeAnnot({ desc = InW(2, i, t) }, Some a) ->
          assert (args = []);
          let tenc = build_annotatedterm ctx t [] in
          let branch = Llvm.const_int (Llvm.integer_type context 1) i in
          let attrib_branch = Bitvector.concat tenc.attrib (Bitvector.of_list [branch]) in
          let denc = { payload = tenc.payload; attrib = attrib_branch} in
            build_truncate_extend denc a
      | CaseW({ desc = TypeAnnot(u, Some a) }, [(x, s); (y, t)]) -> 
          let uenc = build_annotatedterm ctx u [] in
          let ax, ay = 
            match Type.finddesc a with
              | Type.SumW [ax; ay] -> ax, ay
              | _ -> assert false in
          assert (Bitvector.length uenc.attrib > 0);
          let xya, cond = Bitvector.takedrop (Bitvector.length (uenc.attrib) - 1) uenc.attrib in
          let xyenc = {payload = uenc.payload; attrib = xya } in
          let xenc = build_truncate_extend xyenc ax in
          let yenc = build_truncate_extend xyenc ay in
          let func = Llvm.block_parent (Llvm.insertion_block builder) in
          let block_s = Llvm.append_block context "case_l" func in 
          let block_t = Llvm.append_block context "case_r" func in 
          let block_res = Llvm.append_block context "case_res" func in
          let cond' = Bitvector.extractvalue cond 0 in
            ignore (Llvm.build_cond_br cond' block_t block_s builder);
            Llvm.position_at_end block_s builder;
            (* may generate new blocks! *)
            let senc = build_annotatedterm ((x, xenc) :: ctx) s args in
            let _ = Llvm.build_br block_res builder in
            let block_end_s = Llvm.insertion_block builder in
              Llvm.position_at_end block_t builder;
              let tenc = build_annotatedterm ((y, yenc) :: ctx) t args in
              let _ = Llvm.build_br block_res builder in
              let block_end_t = Llvm.insertion_block builder in
                assert ((Bitvector.length senc.attrib) = (Bitvector.length tenc.attrib));
                (* insert phi nodes in result *)
                Llvm.position_at_end block_res builder;
                let z_attrib = Bitvector.build_phi 
                                 [(senc.attrib, block_end_s); 
                                  (tenc.attrib, block_end_t)]
                                 builder in
                let z_payload = 
                  List.map 
                    (fun (x,y) -> 
                       if x == y then x 
                       else Llvm.build_phi [(x, block_end_s);
                                            (y, block_end_t)] "z" builder)
                    (List.combine senc.payload tenc.payload) in
                  {payload = z_payload; attrib = z_attrib}
      | LoopW(u, (x, { desc = TypeAnnot(t, Some a) })) -> 
          let ax, ay = 
            match Type.finddesc a with
              | Type.SumW [ax; ay] -> ax, ay
              | _ -> assert false in
          let uenc = build_annotatedterm ctx u [] in
          let block_init = Llvm.insertion_block builder in                             
          let func = Llvm.block_parent (Llvm.insertion_block builder) in
          let block_loop = Llvm.append_block context "loop" func in 
            let _ = Llvm.build_br block_loop builder in
            Llvm.position_at_end block_loop builder;
          let z_payload = 
            List.map (fun x -> Llvm.build_phi [(x, block_init)] "z" builder)
              uenc.payload in
          let z_attrib = Bitvector.build_phi [(uenc.attrib, block_init)] builder in
          let xenc = { payload = z_payload; attrib = z_attrib } in
          let tenc = build_annotatedterm ((x, xenc) :: ctx) t [] (* TODO *) in 
          assert (Bitvector.length tenc.attrib > 0);
          let xya, cond = Bitvector.takedrop (Bitvector.length (tenc.attrib) - 1) tenc.attrib in
          let xyenc = {payload = tenc.payload; attrib = xya } in
          let xenc = build_truncate_extend xyenc ax in
          let yenc = build_truncate_extend xyenc ay in
          let block_res = Llvm.append_block context "case_res" func in
          let cond' = Bitvector.extractvalue cond 0 in
            ignore (Llvm.build_cond_br cond' block_loop block_res builder);
            let block_curr = Llvm.insertion_block builder in 
            List.iter (fun (y, phinode) ->
                         Llvm.add_incoming (y, block_curr) phinode)
              (List.combine yenc.payload z_payload);
            Bitvector.add_incoming (yenc.attrib, block_curr) z_attrib;
            Llvm.position_at_end block_res builder;
              xenc
      | FoldW((alpha, a), t) ->
          let tenc = build_annotatedterm ctx t args in
          let i64 = Llvm.i64_type context in
          let i1 = Llvm.i1_type context in
          let malloctype = Llvm.function_type 
                             (Llvm.pointer_type (Llvm.i8_type context)) 
                             (Array.of_list [i64]) in
          let malloc = Llvm.declare_function "malloc" malloctype the_module in
          let mua = Type.newty (Type.MuW(alpha, a)) in
          let a_unfolded = Type.subst (fun beta -> if Type.equals beta alpha then mua else beta) a in
          let len_p = payload_size a_unfolded in
          let len_a = attrib_size a_unfolded in
          let a_struct_members = Array.append (Array.make len_p i64) (Array.make len_a i1) in
          let a_struct = Llvm.packed_struct_type context a_struct_members in
          assert (len_p = List.length tenc.payload);
          assert (len_a = Bitvector.length tenc.attrib);
          let struct_content = 
            (List.combine (Listutil.init len_p (fun i -> i)) tenc.payload) @
            (Listutil.init len_a (fun i -> (len_p + i, Bitvector.extractvalue tenc.attrib i))) in
          let t_struct = 
            List.fold_right 
              (fun (i,v) s -> Llvm.build_insertvalue s v i "tstruct" builder) 
              struct_content 
              (Llvm.undef a_struct) in
          let mem_i8ptr = Llvm.build_call malloc (Array.of_list [Llvm.size_of a_struct]) 
                            "memi8" builder in
          let mem_a_struct_ptr = Llvm.build_bitcast mem_i8ptr (Llvm.pointer_type a_struct) 
                                   "memstruct" builder in
          ignore (Llvm.build_store t_struct mem_a_struct_ptr builder);
          let pl = Llvm.build_ptrtoint mem_a_struct_ptr i64 "memint" builder in
            {payload = [pl]; attrib = Bitvector.null 0}
      | UnfoldW((alpha, a), t) ->
          let i64 = Llvm.i64_type context in
          let i1 = Llvm.i1_type context in
          let freetype = Llvm.function_type (Llvm.void_type context) (Array.of_list [i64]) in
          let free = Llvm.declare_function "free" freetype the_module in
          let mua = Type.newty (Type.MuW(alpha, a)) in
          let a_unfolded = Type.subst (fun beta -> if Type.equals beta alpha then mua else beta) a in
          let len_p = payload_size a_unfolded in
          let len_a = attrib_size a_unfolded in
          let a_struct_members = Array.append (Array.make len_p i64) (Array.make len_a i1) in
          let a_struct = Llvm.packed_struct_type context a_struct_members in
            begin
              match build_annotatedterm ctx t args with
                | {payload = [tptrint]; attrib = a } when Bitvector.length a = 0 ->
                    let tptr = Llvm.build_inttoptr tptrint (Llvm.pointer_type a_struct) "tptr" builder in
                    let tstruct = Llvm.build_load tptr "tstruct" builder in
                    ignore (Llvm.build_call free (Array.of_list [tptrint]) "" builder);
                    let pl = Listutil.init len_p (fun i -> Llvm.build_extractvalue tstruct i "p" builder) in
                    let at = Listutil.init len_a (fun i -> Llvm.build_extractvalue tstruct (len_p + i) "p" builder) in
                      {payload = pl; attrib = Bitvector.of_list at}
                | _ -> assert false
            end
      | TypeAnnot(t, _) ->
          build_annotatedterm ctx t args
      | AppW(t1, t2) ->
          let t2enc = build_annotatedterm ctx t2 [] in
            build_annotatedterm ctx t1 (t2enc :: args)
      | LambdaW((x, a), t1) ->
          (match args with
             | [] -> failwith "all functions must be fully applied"
             | t2enc :: args' ->
                 build_annotatedterm ((x, t2enc) :: ctx) t1 args')
      | _ -> 
          Printf.printf "%s\n" (Printing.string_of_termW t);
          failwith "TODO"
  in
  let t_annotated = mkTypeAnnot (freshen_type_vars (annotate_term t)) (Some a) in
 (*   Printf.printf "%s\n" (Printing.string_of_termW t_annotated); *)
  let _ = Typing.principal_typeW type_ctx t_annotated in    
    build_annotatedterm ctx t_annotated []

let rec isPure (t: Term.t) : bool =
  match t.Term.desc with
    | Var(_) -> true
    | UnitW -> true
    | ConstW(Cbot) | ConstW(Cprint(_)) | ConstW(Cintprint)-> false
    | ConstW(Cintconst(_)) | ConstW(Cintadd) | ConstW(Cintsub) | ConstW(Cintmul)
    | ConstW(Cintdiv) (* questionable! *) | ConstW(Cinteq) | ConstW(Cintslt) -> true
    | FoldW(_, t) -> isPure t
    | InW(i, j, s) -> isPure s
    | PairW(t1, t2) -> isPure t1 && (isPure t2)
    | LambdaW(_) -> true
    | AppW(t1, t2) -> isPure t1 && (isPure t2)
    | CaseW(s, [(u, su); (v, sv)]) -> isPure s && (isPure su) && (isPure sv)
    | _ -> false

let rec reduce (t : Term.t) : Term.t =
    match t.Term.desc with
      | Var(_) | ConstW(_) | UnitW | LoopW(_) | FoldW(_) |  LambdaW(_) -> t
      | TypeAnnot(t, a) ->
          mkTypeAnnot (reduce t) a
      | InW(i, j, t) -> mkInW i j (reduce t)
      | UnfoldW(_, {desc = FoldW(_, t)}) -> reduce t
      | UnfoldW(_) -> t
      | PairW(t1, t2) ->
          mkPairW (reduce t1) (reduce t2)
      | LetW(t1, (x, y, t2)) ->
          let rt1 = reduce t1 in
            begin
              match rt1.Term.desc with
                | PairW(s1, s2) when isPure rt1 ->
                    (* Need to be careful to avoid accidental capture. *)
                    let x' = fresh_var () in
                    let y' = fresh_var () in
                    let t' = Term.rename_vars (fun z -> if z = x then x' else if z = y then y' else z) t2 in
                      reduce (Term.subst s1 x' (Term.subst s2 y' t'))
                | _ -> mkLetW rt1 ((x, y), reduce t2)
            end
      | CaseW(s, [(u, su); (v, sv)]) ->
          let rs = reduce s in
            begin
            match rs.Term.desc with
              | InW(2, 0, rs0) when isPure rs ->
                  reduce (Term.subst rs0 u su)
              | InW(2, 1, rs1) when isPure rs ->
                  reduce (Term.subst rs1 v sv)
              | LetW(t1, (x, y, t2)) ->
                  let x' = fresh_var () in
                  let y' = fresh_var () in
                  let t2' = Term.rename_vars (fun z -> if z = x then x' else if z = y then y' else z) t2 in
                    mkLetW t1 ((x',y'), reduce (mkCaseW t2' [(u, su); (v, sv)]))
              | _ -> 
                  Printf.printf "%s\n" (Printing.string_of_termW rs);
                  mkCaseW rs [(u, su); (v, sv)]
            end
      | AppW(t1, t2) ->
          let rt1 = reduce t1 in
          let rt2 = reduce t2 in
            begin
            match rt1.Term.desc with
              | LambdaW((x, a), f) when isPure rt2 ->
                  reduce (Term.subst rt2 x f)
              | _ -> 
                  mkAppW rt1 rt2
            end
      | _ -> 
          Printf.printf "%s\n" (Printing.string_of_termW t);
          failwith "TODO"

type wire_end = { 
  anchor: int; 
  message_type: Type.t
}

type let_bindings = (Term.t * (Term.var * Term.var)) list 
type connection = 
    Dead_End of wire_end
  | Direct of wire_end * let_bindings * (Term.t * Term.t) * wire_end
  | Branch of wire_end * let_bindings * (Term.t * (Term.t * (Term.var * Term.t * wire_end) * (Term.var * Term.t * wire_end)))

let mkFstWs t = 
  match t.Term.desc with
    | PairW(t1, t2) -> t1
    | _ -> mkFstW t

let mkSndWs t = 
  match t.Term.desc with
    | PairW(t1, t2) -> t2
    | _ -> mkSndW t

let trace (output : wire) (is : instruction list) : connection list =
  (* Supply of fresh variable names. 
   * (The instructions do not contain a free variable starting with "x")
   *)
  let unTensorW a =
    match Type.finddesc a with
      | Type.TensorW(a1, a2) -> a1, a2
      | _ -> assert false in
  let node_map_by_src = 
    let rec build_dst_map i =
      match i with
        | [] -> IntMap.empty
        | node :: rest -> 
            List.fold_right (fun w map -> IntMap.add w.src node map) 
              (wires [node]) (build_dst_map rest) 
    in build_dst_map is in
  let rec trace src dst lets (sigma, v) =
    let unpair t lets =
      match t.Term.desc with
        | PairW(x, y) -> (x, y), lets
        | _ -> 
            let x = fresh_var () in
            let y = fresh_var () in
              (mkVar x, mkVar y), (t, (x, y)) :: lets in
    let rec make_bindings t (vars, f) =
      match vars with 
        | [] -> [], mkUnitW, f
        | x :: rest ->
            let th = fresh_var () in
            let tr = fresh_var () in
            let f' = Term.rename_vars (fun u -> if u = x then tr else u) f in
            let lets, t', f'' = make_bindings (mkVar th) (rest, f') in
              lets @ [(t, (th, tr))], mkPairW t' (mkVar tr), f'' in
      if not (IntMap.mem dst node_map_by_src) then
        begin
          if dst = output.dst then
            Direct(src, lets, (sigma, v), {anchor = dst; message_type = output.type_forward}) 
          else 
            Dead_End(src)
        end
      else 
        match IntMap.find dst node_map_by_src with
          | Axiom(w1 (* [f] *), f) when dst = w1.src ->
              let newlets, sigma', f' = make_bindings sigma f in
                trace src w1.dst (newlets @ lets) (sigma', reduce (mkAppW f' v))
          (*            Direct(src, newlets @ lets, 
           (sigma', mkAppW f' v), 
           {anchor = w1.dst; message_type = w1.type_forward})*)
          | Tensor(w1, w2, w3) when dst = w1.src -> 
              (* <sigma, v> @ w1       |-->  <sigma, inl(v)> @ w3 *)
              trace src w3.dst lets (sigma, mkInlW v)
          | Tensor(w1, w2, w3) when dst = w2.src -> 
              (* <sigma, v> @ w2       |-->  <sigma, inr(v)> @ w3 *)
              trace src w3.dst lets (sigma, mkInrW v)
          | Tensor(w1, w2, w3) when dst = w3.src -> 
              (* <sigma, inl(v)> @ w3  |-->  <sigma, v> @ w1
               <sigma, inr(v)> @ w3  |-->  <sigma, v> @ w2 *)
              begin
                match v.Term.desc with
                  | InW(2, 0, v') -> trace src w1.dst lets (sigma, v')
                  | InW(2, 1, v') -> trace src w2.dst lets (sigma, v')
                  | _ -> 
                      let v' = "v'" in 
                        (*                      assert (Type.equals src.message_type w3.type_back);*)
                        Branch(src, lets,
                               (sigma, (v, 
                                        (v', mkVar v', {anchor = w1.dst; message_type = w1.type_forward}), 
                                        (v', mkVar v', {anchor = w2.dst; message_type = w2.type_forward}))))
              end
            | Der(w1 (* \Tens A X *), w2 (* X *), f) when dst = w1.src ->
                trace src w2.dst lets (sigma, mkSndWs v)
                | Der(w1 (* \Tens A X *), w2 (* X *), f) when dst = w2.src ->
                    let newlets, sigma', f' = make_bindings sigma f in
                      trace src w1.dst (newlets @ lets) (sigma', mkPairW f' v)
                | Door(w1 (* X *), w2 (* \Tens A X *)) when dst = w1.src ->
                    let (sigma', c), lets' = unpair sigma lets in
                      trace src w2.dst lets' (sigma', mkPairW c v)
                | Door(w1 (* X *), w2 (* \Tens A X *)) when dst = w2.src ->
                    let (c, v'), lets' = unpair v lets in
                      trace src w1.dst lets' (mkPairW sigma c, v')
                | ADoor(w1 (* \Tens (A x B) X *), w2 (* \Tens B X *)) when dst = w1.src ->
                    let (dc, v'), lets' = unpair v lets in
                    let (d, c), lets'' = unpair dc lets' in
                      trace src w2.dst lets'' (mkPairW sigma d, mkPairW c v')
                | ADoor(w1 (* \Tens (A x B) X *), w2 (* \Tens B X *)) when dst = w2.src ->
                    let (sigma', d), lets' = unpair sigma lets in
                    let (c, v'), lets'' = unpair v lets' in
                      trace src w1.dst lets' (sigma', mkPairW (mkPairW d c) v')
                | LWeak(w1 (* \Tens A X *), 
                        w2 (* \Tens B X *)) (* B <= A *) when dst = w1.src ->
                    let _, a_token = unTensorW w1.type_back in
                    let a, _ = unTensorW a_token in
                    let _, b_token = unTensorW w2.type_forward in
                    let b, _ = unTensorW b_token in
                    let (c, v'), lets' = unpair v lets in
                      trace src w2.dst lets' (sigma, reduce (mkPairW (mkAppW (project b a) c) v'))
                | LWeak(w1 (* \Tens A X *), 
                        w2 (* \Tens B X *)) (* B <= A *) when dst = w2.src ->
                    let _, a_token = unTensorW w1.type_forward in
                    let a, _ = unTensorW a_token in
                    let _, b_token = unTensorW w2.type_back in
                    let b, _ = unTensorW b_token in
                    let (c, v'), lets' = unpair v lets in
                      trace src w1.dst lets' (sigma, reduce (mkPairW (mkAppW (embed b a) c) v'))
                | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) when dst = w3.src ->
                    (*   <sigma, *> @ w3      |-->  <sigma, *> @ w1 *)
                    trace src w1.dst lets (sigma, mkUnitW)
                | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) when dst = w1.src ->
                    (* <sigma, v> @ w1      |-->  <sigma, <v,*>> @ w2 *)
                    trace src w2.dst lets (sigma, mkPairW v mkUnitW)
                | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) when dst = w2.src ->
                    (* <sigma, <v,w>> @ w2  |-->  <sigma, w> @ w3 *)
                    trace src w3.dst lets (sigma, mkSndWs v)
                | Contr(w1, w2, w3) when dst = w2.src -> 
                    (*  <sigma, <v,w>> @ w2         |-->  <sigma, <inl(v),w>> @ w1 *) 
                    let (c, v'), lets' = unpair v lets in
                      trace src w1.dst lets' (sigma, mkPairW (mkInlW c) v')
                | Contr(w1, w2, w3) when dst = w3.src -> 
                    (* <sigma, <v,w>> @ w3         |-->  <sigma, <inr(v),w>> @ w1 *)
                    let (c, v'), lets' = unpair v lets in
                      trace src w1.dst lets' (sigma, mkPairW (mkInrW c) v')
                | Contr(w1, w2, w3) when dst = w1.src -> 
                    (*   <sigma, <inl(v), w>> @ w1   |-->  <sigma, <v,w>> @ w2
                     <sigma, <inr(v), w>> @ w1   |-->  <sigma, <v,w>> @ w3 *)
                    begin
                      let (c', v'), lets' = unpair v lets in
                        match c'.Term.desc with
                          | InW(2, 0, c) -> trace src w2.dst lets' (sigma, mkPairW c v')
                          | InW(2, 1, c) -> trace src w3.dst lets' (sigma, mkPairW c v')
                          | _ ->
                              let c = Term.variant_var_avoid "c" (Term.free_vars v') in
                                (*                      assert (Type.equals src.message_type w1.type_back); *)
                                Branch(src, lets', 
                                       (sigma, (c', 
                                                (c, mkPairW (mkVar c) v', {anchor = w2.dst; message_type = w2.type_forward}),
                                                (c, mkPairW (mkVar c) v', {anchor = w3.dst; message_type = w3.type_forward}))))
                    end
                | _ -> assert false
  in
  let sigma, x = "sigma", "x" in
  let entry_points = Hashtbl.create 10 in
  let rec trace_all src =
    if not (Hashtbl.mem entry_points src.anchor) then 
      let c = trace src src.anchor [] (mkVar sigma, mkVar x) in
        Hashtbl.add entry_points src.anchor ();
        match c with
          | Dead_End(_) -> [c]
          | Direct(_, _, _, dst) ->
              c :: (if dst.anchor = output.dst then [] else trace_all dst)
          | Branch(_, _, (_, (_, (_, _, dst1), (_, _, dst2)))) ->
              c :: trace_all dst1 @ trace_all dst2 
              else [] 
  in
    trace_all {anchor = output.src; message_type = output.type_back}

let build_connections (the_module : Llvm.llmodule) (func : Llvm.llvalue) 
      (connections : connection list) (entry:int) (exit:int) : unit =
  let blocks = Hashtbl.create 10 in
  let phi_nodes = Hashtbl.create 10 in    
  let get_block anchor =
    try
      Hashtbl.find blocks anchor
    with Not_found ->
      let label = Printf.sprintf "L%i" anchor in
      let block = Llvm.append_block context label func in
        Hashtbl.add blocks anchor block;
        block in
  let connect_to src_block encoded_value dst =
    try 
      let phi = Hashtbl.find phi_nodes dst in
        List.iter 
          (fun (phix, x) -> Llvm.add_incoming (x, src_block) phix)
          (List.combine phi.payload encoded_value.payload);
        Bitvector.add_incoming (encoded_value.attrib, src_block) phi.attrib
        (* add (encoded_value, source) to phi node *)
    with Not_found ->
      (* TODO: Bei Grad 1 braucht man keine Phi-Knoten *)
      begin
        position_at_start (get_block dst) builder;
        let payload = List.map (fun x -> Llvm.build_phi [(x, src_block)] "g" builder) encoded_value.payload in
        let attrib = Bitvector.build_phi [(encoded_value.attrib, src_block)] builder in
        let phi = { payload = payload; attrib = attrib } in
          Hashtbl.add phi_nodes dst phi
      end
      (* add new phi node with (encoded_value, source) to block dst *)
  in
  let rec mkLets lets t =
    match lets with
      | [] -> t
      | (s, (x, y)) :: lets' -> mkLets lets' (mkLetW s ((x, y), t)) 
  in
    (* make entry block *)
    Llvm.position_at_end (get_block entry) builder;
    connect_to (get_block entry) { payload = []; attrib = Bitvector.null 0 } entry;
    (* build unconnected blocks *)
    List.iter (fun c ->
                 match c with
                   | Dead_End(src) -> 
(*                       Printf.printf "%i --> \n" src.anchor; *)
                       Llvm.position_at_end (get_block src.anchor) builder;
                       let senc = Hashtbl.find phi_nodes src.anchor in
                       ignore (Llvm.build_br (get_block src.anchor) builder);
                         connect_to (get_block src.anchor) senc src.anchor
                   | Direct(src, lets, (sigma, t) , dst) ->
(*                       Printf.printf "%i --> %i\n" src.anchor dst.anchor;
                       Printf.printf "%s\n--\n%s\n===\n\n"
                         (Printing.string_of_termW sigma)
                         (Printing.string_of_termW (reduce t)); 
                       flush stdout;*)
                       Llvm.position_at_end (get_block src.anchor) builder;
                       let senc = Hashtbl.find phi_nodes src.anchor in
                       let t = mkLetW (mkVar "z") (("sigma", "x"), mkLets lets (mkPairW sigma t)) in
                       let ev = build_term the_module 
                                  [("z", senc)] [("z", src.message_type)] (reduce t) dst.message_type in
                       let src_block = Llvm.insertion_block builder in
                         ignore (Llvm.build_br (get_block dst.anchor) builder);
                         connect_to src_block ev dst.anchor
                   | Branch(src, lets, (sigma, (s, (xl, tl, dst1), (xr, tr, dst2)))) ->
(*                       Printf.printf "%i --> %i | %i\n" src.anchor dst1.anchor dst2.anchor;
                       flush stdout; *)
                       begin
                         let t = mkLetW (mkVar "z") (("sigma", "x"), mkLets lets (
                                                     mkCaseW s 
                                                       [(xl, mkInlW (mkPairW sigma tl)) ;
                                                        (xr, mkInrW (mkPairW sigma tr)) ])) in
(*                       Printf.printf "%s\n--\n%s\n===\n\n"
                         (Printing.string_of_termW sigma)
                         (Printing.string_of_termW (reduce t)); *)
                         let src_block = get_block src.anchor in
                           Llvm.position_at_end src_block builder;
                           let senc = Hashtbl.find phi_nodes src.anchor in
                           let tenc = build_term the_module [("z", senc)] [("z", src.message_type)] (reduce t)
                                        (Type.newty (Type.SumW[dst1.message_type; dst2.message_type])) in
                           let da, cond = Bitvector.takedrop (Bitvector.length tenc.attrib - 1) tenc.attrib in
                           let denc12 = { payload = tenc.payload; attrib = da } in
                           let denc1 = build_truncate_extend denc12 dst1.message_type in
                           let denc2 = build_truncate_extend denc12 dst2.message_type in
                           let cond' = Bitvector.extractvalue cond 0 in
                           let src_block = Llvm.insertion_block builder in
                             ignore (Llvm.build_cond_br cond' (get_block dst2.anchor) 
                                       (get_block dst1.anchor) builder);
                             connect_to src_block denc1 dst1.anchor;
                             connect_to src_block denc2 dst2.anchor
                       end)                         
      connections;
    (* make return *)
    Llvm.position_at_end (get_block exit) builder;
    ignore (Llvm.build_ret_void builder)


let build_body (the_module : Llvm.llmodule) func (c : circuit) =
  let instructions_fresh = 
    let prep_var_y x = "y" ^ x in
    let prep_y (sigma, f) =
      (List.map prep_var_y sigma, rename_vars prep_var_y f) in
    let rec i_fresh instructions = 
      match instructions with
        | [] -> []
        | Der(w1, w2, (sigma, f)) :: rest -> 
            Der(w1, w2, prep_y (sigma, f)) :: (i_fresh rest)
        | Axiom(w, (sigma, f)) :: rest ->
            Axiom(w, prep_y (sigma, f)) :: (i_fresh rest)
        | node :: rest -> 
            node :: (i_fresh rest) in
      i_fresh c.instructions in
  let connections = trace c.output instructions_fresh in 
    build_connections the_module func connections c.output.src c.output.dst

(* Must be applied to circuit of type [A] *)    
let llvm_circuit (c : Compile.circuit) = 
  let the_module = Llvm.create_module context "intml" in
  let void = Llvm.void_type context in
  let ft = Llvm.function_type void (Array.make 0 void) in
  let f = Llvm.declare_function "main" ft the_module in
    build_body the_module f c;
(*    Llvm.dump_module the_module; *)
    the_module
