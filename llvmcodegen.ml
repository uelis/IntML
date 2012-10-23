(* TODO: 
 * - rename nat => int
 * - operations on int (+,*,/,print)
 * - remove succ
 * - list-type
 *)
open Term
open Compile

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

  (* TODO: document properly *)
  val mk_dummy : int -> t * (Llvm.llvalue * Llvm.llvalue) list
  val build_phi: (t * Llvm.llbasicblock) list -> Llvm.llbuilder -> t
  val add_incoming: t * Llvm.llbasicblock -> t -> unit
  val replace_all_uses : Llvm.llvalue -> Llvm.llvalue -> t -> t 
  val llvalue_replacement : t -> t -> (Llvm.llvalue * Llvm.llvalue) list
end = 
struct
  type t = { 
    vector : Llvm.llvalue option;
    len : int
  }

  let struct_type len =
    Llvm.vector_type (Llvm.i1_type context) len

  let mk_dummy len = 
    if len = 0 then 
      { vector = None; len = 0 }, []
    else 
      let vi1 = Llvm.vector_type  (Llvm.i1_type context) len in
      let dummy0 = Llvm.build_alloca vi1 "dummy" builder in
      let dummy = Llvm.build_bitcast dummy0 vi1 "dummy" builder in
        { vector = Some dummy; len = len },
        [ (dummy, Llvm.const_null vi1) ]
              
  let length b = b.len

  let undef len = 
    if len = 0 then 
      { vector = None; len = 0 }
    else 
      { vector = Some (Llvm.undef (struct_type len)); 
        len = len }

  let null len = 
    if len = 0 then 
      { vector = None; len = 0 }
    else 
      { vector = Some (Llvm.const_null (struct_type len)); 
        len = len }

  let values_of_struct s len =
    Listutil.init len (fun i -> 
                     Llvm.build_extractelement s (Llvm.const_int (Llvm.i32_type context) i) "i" builder)

      (* bl darf nicht leer sein *)
  let struct_of_list bl =
    let len = List.length bl in
    let s = Llvm.const_null (struct_type len) in
    let ibl = List.combine (Listutil.init len (fun i -> i)) bl in
      List.fold_right (fun (i,v) s ->
                         Llvm.build_insertelement s v (Llvm.const_int (Llvm.i32_type context) i) "x" builder)
        ibl s
 
  let concat b1 b2 = 
    match b1.vector, b2.vector with
      | None , _ -> b2
      | _, None -> b1
      | Some v1, Some v2 -> 
          { vector = Some (struct_of_list ((values_of_struct v1 b1.len) @ (values_of_struct v2 b2.len))); 
            len = b1.len + b2.len }

  let takedrop n b1 =
    if n = 0 then { vector = None; len = 0 } , b1 
    else if n = b1.len then b1, { vector = None; len = 0 } 
    else 
      match b1.vector with 
        | None -> assert false
        | Some z -> 
            let vs = values_of_struct z b1.len in
            let h, t = Listutil.part n vs in
              { vector = Some (struct_of_list h); len = n },
              { vector = Some (struct_of_list t); len = b1.len - n }

  let extractvalue b i =    
    match b.vector with
      | Some v -> Llvm.build_extractelement v (Llvm.const_int (Llvm.i32_type context) i) "e" builder
      | None -> assert false

  let of_list bl =
    let len = List.length bl in
      if len = 0 then 
        { vector = None; len = 0 }
      else
        { vector = Some (struct_of_list bl); len = len }

  let build_phi vecblocks builder =
    match vecblocks with
      | ({ vector = Some vx; len = lx }, blockx) :: rest ->
          let z = Llvm.build_phi [(vx, blockx)] "z" builder in
            List.iter (function 
                         | ({ vector = Some vy }, blocky) -> 
                             Llvm.add_incoming (vy, blocky) z
                         | _ -> assert false) rest;
            { vector = Some z; len = lx }
      | ({ vector = None }, blockx) :: rest ->
          { vector = None; len = 0} 
      | _ ->
          assert false

  let add_incoming (y, blocky) x =
    match x.vector, y.vector with
      | Some vx, Some vy -> Llvm.add_incoming (vy, blocky) vx
      | _ -> ()

  let replace_all_uses oldv newv b =
    { vector = 
        (match b.vector with
          | None -> None
          | Some v -> Some (if v == oldv then newv else v));
      len = b.len
    } 

  let llvalue_replacement oldb newb = 
   match oldb.vector, newb.vector with
     | Some ov, Some nv -> [(ov, nv)]
     | _ -> []
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

let entry_points : (int, Llvm.llbasicblock) Hashtbl.t = Hashtbl.create 10                                                         
let token_names : (int, encoded_value) Hashtbl.t = Hashtbl.create 10
let token_zero_init : ((Llvm.llvalue * Llvm.llvalue) list) ref = ref []

let clear_tables () =
  Hashtbl.clear entry_points;
  Hashtbl.clear token_names;
  token_zero_init := []

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


let replace_in_token_names (oldv : Llvm.llvalue) (newv : Llvm.llvalue)  =
  let replace (token_name : encoded_value) =
    let payload = List.map (fun v -> if v == oldv then newv else v) token_name.payload in 
    let attrib = Bitvector.replace_all_uses oldv newv token_name.attrib in
      { payload = payload; attrib = attrib } in
    (* TODO: inefficient *)
  let bindings = Hashtbl.fold (fun n token bdgs -> (n,token)::bdgs) token_names [] in
    Hashtbl.clear token_names;
    List.iter (fun (n, token) -> Hashtbl.add token_names n (replace token)) bindings

let reduce (is : instruction list) : instruction list =    
  let node_map_by_src = 
    let rec build_dst_map i =
      match i with
        | [] -> IntMap.empty
        | node :: rest -> 
            List.fold_right (fun w map -> IntMap.add w.src node map) 
              (wires [node]) (build_dst_map rest) 
    in build_dst_map is in
  let shortcut_redex w =
    try
    match IntMap.find w.dst node_map_by_src with 
       | Tensor(w1, w2, w3) ->
          (match IntMap.find w3.dst node_map_by_src with
            | Tensor(w1', w2', w3') when w3'.dst = w3.src -> 
                if w.dst = w1.src then {w with dst = w1'.dst}
                else if w.dst = w2.src then {w with dst = w2'.dst}
                else w
            | _ -> w)
       |  _ -> w 
    with Not_found -> w in
  let remove i = 
    match i with 
       | Tensor(w1, w2, w3) ->
          (match IntMap.find w3.dst node_map_by_src with
            | Tensor(w1', w2', w3') when w3'.dst = w3.src -> 
                (try 
                  ignore (IntMap.find w1.dst node_map_by_src);
                  ignore (IntMap.find w2.dst node_map_by_src);
                  false
                with Not_found -> true)
            | _ -> true)
       |  _ -> true in 
  let ris = List.filter remove 
      (List.map (map_wires_instruction shortcut_redex) is) in
   Printf.printf "%i => %i\n" (List.length is) (List.length ris); flush stdout; ris


let allocate_tables (is : instruction list) =
  clear_tables();
  let build_dummy ty name builder = 
     let i0 = Llvm.build_alloca ty name builder in
     let dummy = Llvm.build_bitcast i0 ty name builder in
       token_zero_init := (dummy, Llvm.const_null ty)::!token_zero_init;
       dummy in 
  let add_module n a =
    (try ignore (Hashtbl.find entry_points n) with
       | Not_found ->
           let func = Llvm.block_parent (Llvm.insertion_block builder) in
           let label = Printf.sprintf "L%i" n in
           let block = Llvm.append_block context label func in
             Hashtbl.add entry_points n block;
             (* TODO: clean up *)
             let rec mk_p m = 
               if m = 0 then [] 
               else 
                 (build_dummy (Llvm.i64_type context) "dummy" builder) ::
                 (mk_p (m-1)) in
             let xp = mk_p (payload_size a) in
             let xs = attrib_size a in
             let dummy, zero_init = Bitvector.mk_dummy xs in
               token_zero_init := zero_init @ !token_zero_init;
               Hashtbl.add token_names n { payload = xp; attrib = dummy }
    ) in
  let all_wires = Compile.wires is in
    List.iter 
      (fun w ->
         add_module w.src w.type_back;
         add_module w.dst w.type_forward;
    ) all_wires

type wire_end = { 
  anchor: int; 
  message_type: Type.t
}
type connection = 
    Unconnected
  | Direct of wire_end * (Term.t * Term.t) * wire_end
  | Branch of wire_end * (Term.t * (Term.t * (Term.var * Term.t * wire_end) * (Term.var * Term.t * wire_end)))

let trace (output : wire) (is : instruction list) : connection list =
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
  let rec trace src dst (sigma, v) =
    try
      match IntMap.find dst node_map_by_src with
        | Axiom(w1 (* [f] *), f) when dst = w1.src ->
(*            assert (Type.equals src.message_type w1.type_back); *)
            Direct(src, 
                   (sigma, mkAppW (let_tupleW sigma f) v), 
                    {anchor = w1.dst; message_type = w1.type_forward})
        | Tensor(w1, w2, w3) when dst = w1.src -> 
            (* <sigma, v> @ w1       |-->  <sigma, inl(v)> @ w3 *)
            trace src w3.dst (sigma, mkInlW v)
        | Tensor(w1, w2, w3) when dst = w2.src -> 
            (* <sigma, v> @ w2       |-->  <sigma, inr(v)> @ w3 *)
            trace src w3.dst (sigma, mkInrW v)
        | Tensor(w1, w2, w3) when dst = w3.src -> 
            (* <sigma, inl(v)> @ w3  |-->  <sigma, v> @ w1
             <sigma, inr(v)> @ w3  |-->  <sigma, v> @ w2 *)
            begin
              match v.Term.desc with
                | InW(2, 0, v') -> trace src w1.dst (sigma, v')
                | InW(2, 1, v') -> trace src w2.dst (sigma, v')
                | _ -> 
                    let v' = "v'" in 
(*                      assert (Type.equals src.message_type w3.type_back);*)
                      Branch(src, 
                             (sigma, (v, 
                                      (v', mkVar v', {anchor = w1.dst; message_type = w1.type_forward}), 
                                      (v', mkVar v', {anchor = w2.dst; message_type = w2.type_forward}))))
            end
        | Der(w1 (* \Tens A X *), w2 (* X *), f) when dst = w1.src ->
            trace src w2.dst (sigma, mkSndW v)
        | Der(w1 (* \Tens A X *), w2 (* X *), f) when dst = w2.src ->
            trace src w1.dst (sigma, (mkPairW (let_tupleW sigma f) v))
        | Door(w1 (* X *), w2 (* \Tens A X *)) when dst = w1.src ->
            begin
              match sigma.Term.desc with
                | PairW(sigma', c) -> trace src w2.dst (sigma', mkPairW c v)
                | _ -> 
                    let sigma' = mkFstW sigma in
                    let c = mkSndW sigma in
                    trace src w2.dst (sigma', mkPairW c  v) 
            end
        | Door(w1 (* X *), w2 (* \Tens A X *)) when dst = w2.src ->
            begin
              match v.Term.desc with
                | PairW(c, v') -> trace src w1.dst (mkPairW sigma c, v')
                | _ -> 
                    trace src w1.dst (mkPairW sigma (mkFstW v),
                                      mkSndW v)
            end
        | ADoor(w1 (* \Tens (A x B) X *), w2 (* \Tens B X *)) when dst = w1.src ->
            begin
              match v.Term.desc with
                | PairW({ desc = PairW(d, c) }, v') -> 
                    trace src w2.dst (mkPairW sigma d, mkPairW c v')
                | _ -> 
                    let d = mkFstW (mkFstW v) in
                    let c = mkSndW (mkFstW v) in
                    let v' = mkSndW v in
                      trace src w2.dst (mkPairW sigma d, mkPairW c v')
            end
        | ADoor(w1 (* \Tens (A x B) X *), w2 (* \Tens B X *)) when dst = w2.src ->
            begin
              match sigma.Term.desc, v.Term.desc with
                | PairW(sigma', d), PairW(c, v') -> 
                    trace src w1.dst (sigma', mkPairW (mkPairW d c) v')
                | _ -> 
                    let sigma' = mkFstW sigma in
                    let d = mkSndW sigma in
                    let c = mkFstW v in
                    let v' = mkSndW v in
                      trace src w1.dst (sigma', mkPairW (mkPairW d c) v')
            end
        | LWeak(w1 (* \Tens A X *), 
                w2 (* \Tens B X *)) (* B <= A *) when dst = w1.src ->
            let _, a_token = unTensorW w1.type_back in
            let a, _ = unTensorW a_token in
            let _, b_token = unTensorW w2.type_forward in
            let b, _ = unTensorW b_token in
              begin
                match v.Term.desc with
                  | PairW(c, v') -> 
                      trace src w2.dst (sigma, mkPairW (mkAppW (project b a) c) v')
                  | _ -> 
                      let c = mkFstW v in
                      let v' = mkSndW v in
                        trace src w2.dst (sigma, mkPairW (mkAppW (project b a) c) v')
              end
        | LWeak(w1 (* \Tens A X *), 
                w2 (* \Tens B X *)) (* B <= A *) when dst = w2.src ->
            let _, a_token = unTensorW w1.type_forward in
            let a, _ = unTensorW a_token in
            let _, b_token = unTensorW w2.type_back in
            let b, _ = unTensorW b_token in
              begin
                match v.Term.desc with
                  | PairW(c, v') -> 
                      trace src w1.dst (sigma, mkPairW (mkAppW (embed b a) c) v')
                  | _ -> 
                      let c = mkFstW v in
                      let v' = mkSndW v in
                        trace src w1.dst (sigma, mkPairW (mkAppW (embed b a) c) v')
              end
        | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) when dst = w3.src ->
            (*   <sigma, *> @ w3      |-->  <sigma, *> @ w1 *)
            trace src w1.dst (sigma, mkUnitW)
        | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) when dst = w1.src ->
            (* <sigma, v> @ w1      |-->  <sigma, <v,*>> @ w2 *)
            trace src w2.dst (sigma, mkPairW v mkUnitW)
        | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) when dst = w2.src ->
            (* <sigma, <v,w>> @ w2  |-->  <sigma, w> @ w3 *)
            trace src w3.dst (sigma, mkSndW v)
        | Contr(w1, w2, w3) when dst = w2.src -> 
            (*  <sigma, <v,w>> @ w2         |-->  <sigma, <inl(v),w>> @ w1 *) 
            trace src w1.dst (sigma, mkPairW (mkInlW (mkFstW v)) (mkSndW v))
        | Contr(w1, w2, w3) when dst = w3.src -> 
            (* <sigma, <v,w>> @ w3         |-->  <sigma, <inr(v),w>> @ w1 *)
            trace src w1.dst (sigma, mkPairW (mkInrW (mkFstW v)) (mkSndW v))
        | Contr(w1, w2, w3) when dst = w1.src -> 
            (*   <sigma, <inl(v), w>> @ w1   |-->  <sigma, <v,w>> @ w2
             <sigma, <inr(v), w>> @ w1   |-->  <sigma, <v,w>> @ w3 *)
            begin
              match v.Term.desc with
                | PairW({ desc = InW(2, 0, c) }, v') -> trace src w2.dst (sigma, mkPairW c v')
                | PairW({ desc = InW(2, 1, d) }, v') -> trace src w3.dst (sigma, mkPairW d v')
                | _ ->
                    let v1 = mkFstW v in
                    let v2 = mkSndW v in
                    let v' = Term.variant_var_avoid "v'" (Term.free_vars v2) in
(*                      assert (Type.equals src.message_type w1.type_back); *)
                      Branch(src, 
                             (sigma, (v1, 
                                      (v', mkPairW (mkVar v') v2, {anchor = w2.dst; message_type = w2.type_forward}),
                                      (v', mkPairW (mkVar v') v2, {anchor = w3.dst; message_type = w3.type_forward}))))
            end
        | _ -> assert false
    with Not_found -> 
      if dst = output.dst then
        Direct(src, (sigma, v), {anchor = dst; message_type = output.type_forward}) 
      else 
        Unconnected
  in
  let sigma, x = "sigma", "x" in
  let entry_points = Hashtbl.create 10 in
  let rec trace_all src =
    if not (Hashtbl.mem entry_points src.anchor) then 
      let c = trace src src.anchor (mkVar sigma, mkVar x) in
        Hashtbl.add entry_points src.anchor ();
        match c with
          | Unconnected -> []
          | Direct(_, _, dst) ->
              c :: (if dst.anchor = output.dst then [] else trace_all dst)
          | Branch(_, (_, (_, (_, _, dst1), (_, _, dst2)))) ->
              c :: trace_all dst1 @ trace_all dst2 
    else [] 
  in
    trace_all {anchor = output.src; message_type = output.type_back}

let build_connections (the_module : Llvm.llmodule) (connections : connection list) : unit =
  let sources_table = Hashtbl.create 10 in
  let encode_value src (x, t) dst =
    let src_block = Hashtbl.find entry_points src.anchor in
      Llvm.position_at_end src_block builder;
      let senc = Hashtbl.find token_names src.anchor in
        build_term the_module [(x, senc)] [(x, src.message_type)] t dst.message_type in
  let connect src_block encoded_value dst =
    let dsts = try Hashtbl.find sources_table dst.anchor with Not_found -> [] in
      Hashtbl.replace sources_table dst.anchor ((encoded_value, src_block) :: dsts) in
  let build_br dst = 
    let dst_block = Hashtbl.find entry_points dst in
      Llvm.build_br dst_block builder in    
  let build_cond_br cond tdst fdst= 
    let tdst_block = Hashtbl.find entry_points tdst in
    let fdst_block = Hashtbl.find entry_points fdst in
      Llvm.build_cond_br cond tdst_block fdst_block builder 
  in
    (* build unconnected blocks *)
    List.iter (fun c ->
                 match c with
                   | Unconnected -> ()
                   | Direct(src, (sigma, t) , dst) ->
                       let ev = encode_value src ("z", mkLetW (mkVar "z") (("sigma", "x"), mkPairW sigma t)) dst in
                       let current_block = Llvm.insertion_block builder in
                         connect current_block ev dst;
                         ignore (build_br dst.anchor)
                   | Branch(src, (sigma, (s, (xl, tl, dst1), (xr, tr, dst2)))) ->
                       begin
                         let t = mkLetW (mkVar "z") (("sigma", "x"), 
                                                     mkCaseW s 
                                                       [(xl, mkInlW (mkPairW sigma tl)) ;
                                                        (xr, mkInrW (mkPairW sigma tr)) ]) in
                         let src_block = Hashtbl.find entry_points src.anchor in
                           Llvm.position_at_end src_block builder;
                           let senc = Hashtbl.find token_names src.anchor in
                           let tenc = build_term the_module [("z", senc)] [("z", src.message_type)] t 
                                        (Type.newty (Type.SumW[dst1.message_type; dst2.message_type])) in
                           let da, cond = Bitvector.takedrop (Bitvector.length tenc.attrib - 1) tenc.attrib in
                           let denc12 = { payload = tenc.payload; attrib = da }in
                           let denc1 = build_truncate_extend denc12 dst1.message_type in
                           let denc2 = build_truncate_extend denc12 dst2.message_type in
                           let cond' = Bitvector.extractvalue cond 0 in
                           let current_block = Llvm.insertion_block builder in
                             connect current_block denc1 dst1;
                             connect current_block denc2 dst2;
                             ignore (build_cond_br cond' dst1.anchor dst2.anchor)
                       end)                         
      connections;
    (* connect blocks *)
    let connect_llvm newenc dst =
      let oldenc = Hashtbl.find token_names dst in
        (*      Printf.printf "%i %i -> %i\n" oldenc.attrib_bitlen newenc.attrib_bitlen dst; *)
        assert ((Bitvector.length oldenc.attrib) = (Bitvector.length newenc.attrib));
        assert (List.length oldenc.payload = (List.length newenc.payload));
        List.iter (fun (o, n) -> Llvm.replace_all_uses_with o n) 
          ((List.combine oldenc.payload newenc.payload) @
           (Bitvector.llvalue_replacement oldenc.attrib newenc.attrib)) 
    in
    Hashtbl.iter (fun dst sources ->
                    match sources with
                      | [] -> ()
                      | [(ev, src)] ->
                          connect_llvm ev dst
                      | _ -> 
                          let dstblock = Hashtbl.find entry_points dst in
                            position_at_start dstblock builder;
                              (* Payloads need to be transposed:
                               * [[x1,src1; x2,src1];[x1,src2; x2,src2];[x1,srcr3; x2,srcr3]] 
                               * ->
                               * [[x1,src1; x1,src2; x1,src3];[x2,src1; x2,src2; x3,src3]] *)
                            let payloads = List.map (fun (ev, src_block) ->
                                                       List.map (fun v -> (v, src_block)) 
                                                         ev.payload) 
                                             sources in
                            let attribs = List.map (fun (ev, src_block) -> (ev.attrib, src_block))
                                             sources in
                              (* [[1;2;3];[4;5;6];[7;8;9]] ->
                               * [[1;4;7];[2;5;8];[3;6;9]] *)
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
                                        heads :: transpose tails in
                            let newp = List.map (fun srcs -> Llvm.build_phi srcs "x" builder) (transpose payloads) in
                            let newa = Bitvector.build_phi attribs builder in
                              connect_llvm {payload = newp; attrib = newa } dst)
      sources_table

let build_instruction (the_module : Llvm.llmodule) (i : instruction) : unit =
  let unTensorW a =
    match Type.finddesc a with
      | Type.TensorW(a1, a2) -> a1, a2
      | _ -> assert false in
  let build_br dst = 
    let dst_block = Hashtbl.find entry_points dst in
      Llvm.build_br dst_block builder in    
  let build_cond_br cond tdst fdst= 
    let tdst_block = Hashtbl.find entry_points tdst in
    let fdst_block = Hashtbl.find entry_points fdst in
      Llvm.build_cond_br cond tdst_block fdst_block builder in
    (* w1 and w2 are attached with src to same node. Message arrives on w1,
     * is passed to w2 *)
  let connect1 newenc dst =
    let oldenc = Hashtbl.find token_names dst in
(*      Printf.printf "%i %i -> %i\n" oldenc.attrib_bitlen newenc.attrib_bitlen dst; *)
      assert ((Bitvector.length oldenc.attrib) = (Bitvector.length newenc.attrib));
      assert (List.length oldenc.payload = (List.length newenc.payload));
      Hashtbl.replace token_names dst newenc; 
      List.iter (fun (o, n) -> replace_in_token_names o n) 
        ((List.combine oldenc.payload newenc.payload) @
         (Bitvector.llvalue_replacement oldenc.attrib newenc.attrib));
      List.iter (fun (o, n) -> Llvm.replace_all_uses_with o n) 
        ((List.combine oldenc.payload newenc.payload) @
         (Bitvector.llvalue_replacement oldenc.attrib newenc.attrib)) in
  let connect2 block1 new1enc block2 new2enc dst =
    assert ((Bitvector.length new1enc.attrib) = (Bitvector.length new2enc.attrib));
    let dstblock = Hashtbl.find entry_points dst in
      position_at_start dstblock builder;
    let newp =
      List.map 
        (fun (n1, n2) -> Llvm.build_phi [(n1, block1); (n2, block2)] "xp" builder)
        (List.combine new1enc.payload new2enc.payload) in
    let newa = Bitvector.build_phi [(new1enc.attrib, block1); (new2enc.attrib, block2)] builder in
      connect1 {payload = newp; attrib = newa } dst in
  let build_jump_argument w1 (x, t) w2 =
    let src_block = Hashtbl.find entry_points w1.src in
      Llvm.position_at_end src_block builder;
      let senc = Hashtbl.find token_names w1.src in
      build_term the_module [(x, senc)] [(x, w1.type_back)] t w2.type_forward in
  (* build actual jump with argument *)
  let build_jwa w1 (x, t) w2 =
    let denc = build_jump_argument w1 (x, t) w2 in
      ignore (build_br w2.dst);
      connect1 denc w2.dst
  in
(*  let node_name ins =
        match ins with
          | Axiom(w1, _) -> 
              Printf.sprintf "\"Axiom({%i,%i})\"" w1.src w1.dst
          | Tensor(w1, w2, w3) -> 
              Printf.sprintf "\"Tensor({%i,%i},{%i,%i},{%i,%i})\"" 
                w1.src w1.dst w2.src w2.dst w3.src w3.dst
          | Der(w1, w2, _) -> 
              Printf.sprintf "\"Der({%i,%i},{%i,%i})\"" 
                w1.src w1.dst w2.src w2.dst 
          | Contr(w1, w2, w3) -> 
              Printf.sprintf "\"Contr({%i,%i},{%i,%i},{%i,%i})\"" 
                w1.src w1.dst w2.src w2.dst w3.src w3.dst
          | Door(w1, w2) -> 
              Printf.sprintf "\"Door({%i,%i},{%i,%i})\"" 
                w1.src w1.dst w2.src w2.dst
          | ADoor(w1, w2) -> 
              Printf.sprintf "\"ADoor({%i,%i},{%i,%i})\"" 
                w1.src w1.dst w2.src w2.dst
          | LWeak(w1, w2) -> 
              Printf.sprintf "\"LWeak({%i,%i},{%i,%i})\"" 
                w1.src w1.dst w2.src w2.dst
          | Epsilon(w1, w2, w3) -> 
              Printf.sprintf "\"Epsilon({%i,%i},{%i,%i},{%i,%i})\"" 
                w1.src w1.dst w2.src w2.dst w3.src w3.dst
  in *)
  match i with
   | Axiom(w1 (* [f] *), f) ->
       begin
         let x, sigma, v = "x", "sigma", "v" in
         let t = mkLetW (mkVar x) 
                   ((sigma, v), (mkPairW (mkVar sigma) 
                                   (mkAppW (let_tupleW (mkVar sigma) f) (mkVar v)))) in
           build_jwa w1 (x, t) w1
       end 
   | Tensor(w1, w2, w3) -> 
       let x, sigma, v = "x", "sigma", "v" in
       (* <sigma, v> @ w1       |-->  <sigma, inl(v)> @ w3 *)
       let src1 = Hashtbl.find entry_points w1.src in
       let denc1 =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), (mkPairW (mkVar sigma) (mkInlW (mkVar v)))) in
            build_jump_argument w1 (x, t) w3 in
       (* <sigma, v> @ w2       |-->  <sigma, inr(v)> @ w3 *)
       let src2 = Hashtbl.find entry_points w2.src in
       let denc2 =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), (mkPairW (mkVar sigma) (mkInrW (mkVar v)))) in
            build_jump_argument w2 (x, t) w3 in
       (* insert phi *)         
       connect2 src1 denc1 src2 denc2 w3.dst;
       Llvm.position_at_end src1 builder;
       ignore (build_br w3.dst);
       Llvm.position_at_end src2 builder;
       ignore (build_br w3.dst);
       (* <sigma, inl(v)> @ w3  |-->  <sigma, v> @ w1
          <sigma, inr(v)> @ w3  |-->  <sigma, v> @ w2 *)        
       begin
         let x, sigma, v, c = "x", "sigma", "v", "c" in
         let t = mkLetW (mkVar x) 
                   ((sigma, c), mkCaseW (mkVar c) 
                         [(v, mkInlW (mkPairW (mkVar sigma) (mkVar v))) ;
                          (v, mkInrW (mkPairW (mkVar sigma) (mkVar v))) ]) in
         let src3_block = Hashtbl.find entry_points w3.src in
           Llvm.position_at_end src3_block builder;
           let senc = Hashtbl.find token_names w3.src in
           let tenc = build_term the_module [(x, senc)] [(x, w3.type_back)] t 
                        (Type.newty (Type.SumW[w1.type_forward; w2.type_forward])) in
           let da, cond = Bitvector.takedrop (Bitvector.length tenc.attrib - 1) tenc.attrib in
           let denc12= { payload = tenc.payload; attrib = da }in
           let denc1 = build_truncate_extend denc12 w1.type_forward in
           let denc2 = build_truncate_extend denc12 w2.type_forward in
           let cond' = Bitvector.extractvalue cond 0 in
             connect1 denc1 w1.dst;
             connect1 denc2 w2.dst;
             ignore (build_cond_br cond' w2.dst w1.dst);
       end
   | Der(w1 (* \Tens A X *), w2 (* X *), f) ->
       let x, sigma, v, c = "x", "sigma", "v", "c" in
       begin
         let t = mkLetW (mkVar x) 
                   ((sigma, x), mkLetW (mkVar x) 
                                  ((c, v), (mkPairW (mkVar sigma) (mkVar v)))) in
           build_jwa w1 (x, t) w2
       end;
       begin
         let t = mkLetW (mkVar x) 
                   ((sigma, v), (mkPairW (mkVar sigma) 
                                   (mkPairW (let_tupleW (mkVar sigma) f) (mkVar v)))) in
           build_jwa w2 (x, t) w1
       end 
   | Door(w1 (* X *), w2 (* \Tens A X *)) ->
       let x, sigma, v, c = "x", "sigma", "v", "c" in
       begin
         let t = mkLetW (mkVar x) 
                   ((x, v), mkLetW (mkVar x) 
                              ((sigma, c), (mkPairW (mkVar sigma) (mkPairW (mkVar c) (mkVar v))))) in
           build_jwa w1 (x, t) w2
       end;
       begin
         let t = mkLetW (mkVar x) 
                   ((sigma, x), mkLetW (mkVar x) 
                                  ((c, v), (mkPairW (mkPairW (mkVar sigma) (mkVar c)) (mkVar v)))) in
           build_jwa w2 (x, t) w1
       end
    | ADoor(w1 (* \Tens (A x B) X *), w2 (* \Tens B X *)) ->
       let x, sigma, v, c, d, y = "x", "sigma", "v", "c", "d", "y" in
        begin
          let t = mkLetW (mkVar x) 
                    ((sigma, x), mkLetW (mkVar x) 
                                   ((x, v), mkLetW (mkVar x) 
                                              ((d, c), (mkPairW (mkPairW (mkVar sigma) (mkVar d)) 
                                                          (mkPairW (mkVar c) (mkVar v)))))) in
            build_jwa w1 (x, t) w2
        end;
        begin
          let t = mkLetW (mkVar x) 
                    ((x, y), mkLetW (mkVar x) 
                               ((sigma, d), mkLetW (mkVar y) 
                                              ((c, v), (mkPairW (mkVar sigma) 
                                                          (mkPairW (mkPairW (mkVar d) (mkVar c)) (mkVar v)))))) in
            build_jwa w2 (x, t) w1
        end
    | LWeak(w1 (* \Tens A X *), 
            w2 (* \Tens B X *)) (* B <= A *) ->
       let x, sigma, v, y, c = "x", "sigma", "v", "y", "c" in
       begin
         let _, a_token = unTensorW w1.type_back in
         let a, _ = unTensorW a_token in
         let _, b_token = unTensorW w2.type_forward in
         let b, _ = unTensorW b_token in
         let t = mkLetW (mkVar x) 
                   ((sigma, y), mkLetW (mkVar y) 
                                  ((c, v), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkAppW (project b a) (mkVar c)) 
                                                 (mkVar v))))) in
            build_jwa w1 (x, t) w2
       end;
       begin
         let _, a_token = unTensorW w1.type_forward in
         let a, _ = unTensorW a_token in
         let _, b_token = unTensorW w2.type_back in
         let b, _ = unTensorW b_token in
         let t = mkLetW (mkVar x) 
                   ((sigma, y), mkLetW (mkVar y) 
                                  ((c, v), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkAppW (embed b a) (mkVar c)) 
                                                 (mkVar v))))) in
            build_jwa w2 (x, t) w1
       end
   | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) ->
       let x, sigma, v, c = "x", "sigma", "v", "c" in
       (*   <sigma, *> @ w3      |-->  <sigma, *> @ w1 *)
       begin
         let t = mkLetW (mkVar x) 
                   ((sigma, v), (mkPairW (mkVar sigma) mkUnitW)) in
           build_jwa w3 (x, t) w1
       end;
       (* <sigma, v> @ w1      |-->  <sigma, <v,*>> @ w2 *)
       begin
         let t = mkLetW (mkVar x) ((sigma, v),
                    (mkPairW (mkVar sigma) (mkPairW (mkVar v) mkUnitW))) in
            build_jwa w1 (x, t) w2
       end;
       (* <sigma, <v,w>> @ w2  |-->  <sigma, w> @ w3 *)
       begin
         let t = mkLetW (mkVar x) 
                   ((sigma, x), mkLetW (mkVar x) 
                                  ((c, v), (mkPairW (mkVar sigma) (mkVar v)))) in
            build_jwa w2 (x, t) w3
       end
   | Contr(w1, w2, w3) -> 
       (*  <sigma, <v,w>> @ w2         |-->  <sigma, <inl(v),w>> @ w1 *) 
       let x, sigma, v, y, c, d = "x", "sigma", "v", "y", "c", "d" in
       let src2 = Hashtbl.find entry_points w2.src in
       let denc2 =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), mkLetW (mkVar v) 
                                  ((d, y), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkInlW (mkVar d)) (mkVar y))))) in
            build_jump_argument w2 (x, t) w1 in
       (* <sigma, <v,w>> @ w3         |-->  <sigma, <inr(v),w>> @ w1 *)
       let src3 = Hashtbl.find entry_points w3.src in
       let denc3 =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), mkLetW (mkVar v) 
                                  ((d, y), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkInrW (mkVar d)) (mkVar y))))) in
            build_jump_argument w3 (x, t) w1 in
       connect2 src2 denc2 src3 denc3 w1.dst;
       Llvm.position_at_end src2 builder;
       ignore (build_br w1.dst);
       Llvm.position_at_end src3 builder;
       ignore (build_br w1.dst);

       (*   <sigma, <inl(v), w>> @ w1   |-->  <sigma, <v,w>> @ w2
            <sigma, <inr(v), w>> @ w1   |-->  <sigma, <v,w>> @ w3 *)
       begin
         let t = mkLetW (mkVar x) 
                   ((sigma, v), mkLetW (mkVar v) 
                                  ((c, v), mkCaseW (mkVar c) 
                         [(c, mkInlW (mkPairW (mkVar sigma) (mkPairW (mkVar c) (mkVar v)))) ;
                          (d, mkInrW (mkPairW (mkVar sigma) (mkPairW (mkVar d) (mkVar v)))) ])) in
         let src1_block = Hashtbl.find entry_points w1.src in
           Llvm.position_at_end src1_block builder;
           let senc = Hashtbl.find token_names w1.src in
           let tenc = build_term the_module [(x, senc)] [(x, w1.type_back)] t 
                        (Type.newty (Type.SumW[w2.type_forward; w3.type_forward])) in
           let da, cond = Bitvector.takedrop (Bitvector.length tenc.attrib - 1) tenc.attrib in
           let denc23 = { payload = tenc.payload; attrib = da }in
           let denc2 = build_truncate_extend denc23 w2.type_forward in
           let denc3 = build_truncate_extend denc23 w3.type_forward in
           let cond' = Bitvector.extractvalue cond 0 in
             connect1 denc2 w2.dst;
             connect1 denc3 w3.dst;
             ignore (build_cond_br cond' w3.dst w2.dst)
       end         

let build_body (the_module : Llvm.llmodule) (c : circuit) =
  let connections = trace c.output c.instructions in 
    build_connections the_module connections;
(*  List.iter (build_instruction the_module) c.instructions;*)
  (* empty blocks become self-loops: *)
  Hashtbl.iter 
    (fun n block ->
       match Llvm.instr_begin block with
         | Llvm.At_end(_) -> 
             Llvm.position_at_end block builder;
             ignore (Llvm.build_br block builder)
         | _ -> ()
  ) entry_points;
  (* replace unreachable tokens by zero *)
  List.iter (fun (t, z) -> Llvm.replace_all_uses_with t z) !token_zero_init


(* Must be applied to circuit of type [A] *)    
let llvm_circuit (c : Compile.circuit) = 
  let the_module = Llvm.create_module context "intml" in
  let void = Llvm.void_type context in
  let ft = Llvm.function_type void (Array.make 0 void) in
  let f = Llvm.declare_function "main" ft the_module in
  let entry = Llvm.append_block context "entry" f in
  let dummy = Llvm.append_block context "dummy" f in
    Llvm.position_at_end dummy builder;
(*    let c = {c with instructions = reduce c.instructions} in *)
    allocate_tables c.instructions;
    (* Entry module *)
    Llvm.position_at_end entry builder;
    ignore (Llvm.build_br (Hashtbl.find entry_points c.output.src) builder);
    (* Exit module *)
    Llvm.position_at_end (Hashtbl.find entry_points c.output.dst) builder;
    ignore (Llvm.build_ret_void builder);
    (* body *)
    build_body the_module c;
    Llvm.delete_block dummy; 
    Llvm.dump_module the_module; 
    the_module
