(* TODO: 
 * - rename nat => int
 * - operations on int (+,*,/,print)
 * - remove succ
 * - list-type
 *)
open Term
open Compile

let unTensorW a =
  match Type.finddesc a with
    | Type.TensorW(a1, a2) -> a1, a2
    | _ -> assert false

let rec list_init (n : int) (f : int -> 'a) : 'a list =
   if n <= 0 then [] 
   else f 0 :: (list_init (n-1) (fun i -> f (i+1)))

let part n l =
  let rec part_rev n l =
    if n = 0 then ([], l) else
      let (h,t) = part_rev (n-1) l in
      match t with
        | [] -> raise Not_found
        | x::t' -> (x::h, t')
  in 
  let (h, t) = part_rev n l in
    (List.rev h, t)

let context = Llvm.global_context ()
let builder = Llvm.builder context

(* Encapsulate bit vectors to make it easy to change the llvm-encoding. *)
module Bitvector :
sig 
  type t
  val length : t -> int
  val null : int -> t
  val concat : t -> t -> t
  val takedrop : int -> t -> t * t
  val extractvalue : t -> int -> Llvm.llvalue
  val insertvalue : t -> int -> Llvm.llvalue -> t
  val of_list: Llvm.llvalue list -> t

  (* TODO: document properly *)                                      
  val build_phi: t * Llvm.llbasicblock -> t * Llvm.llbasicblock -> Llvm.llbuilder -> t
  val replace_all_uses_within : Llvm.llvalue -> Llvm.llvalue -> t -> t 
  val value_replacement : t -> t -> (Llvm.llvalue * Llvm.llvalue) list
end = 
struct
  type t = { bits : Llvm.llvalue list }

  let i1 = Llvm.i1_type context

  let length b = List.length b.bits

  let null len = { bits = list_init len (fun _ -> Llvm.const_null i1) }

  let concat b1 b2 = { bits = b1.bits @ b2.bits }

  let takedrop n b1 = 
    let l1, l2 = part n b1.bits in
      { bits = l1 }, { bits = l2 }

  let extractvalue b i =
    match part i b.bits with
      | _, x :: _ -> x
      | _ -> assert false

  let insertvalue b i v =
    match part i b.bits with
      | h, x :: t -> { bits = h @ (v :: t) }
      | _ -> assert false

  let of_list bl = { bits = bl }

  let build_phi (x, blockx) (y, blocky) builder =
    { bits = List.map 
               (fun (xi,yi) -> Llvm.build_phi [(xi, blockx);
                                               (yi, blocky)] "z" builder)
               (List.combine x.bits y.bits) }

  let replace_all_uses_within oldv newv b =
    { bits = List.map (fun v -> if v == oldv then newv else v) b.bits } 

  let value_replacement oldb newb = 
      List.combine oldb.bits newb.bits
end

type encoded_value = {
  payload : Llvm.llvalue list;
  attrib: Bitvector.t
}
  
let position_at_start block builder =
  let block_begin = Llvm.instr_begin block in
    Llvm.position_builder block_begin builder
(*  match block_begin with
    | Llvm.At_end(_) -> 
        Llvm.position_builder block_begin builder
    | Llvm.Before(i) -> 
        if Llvm.instr_opcode i = Llvm.Opcode.PHI then
          Llvm.position_builder (Llvm.instr_succ i) builder
        else 
          Llvm.position_builder block_begin builder*)

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
let all_tokens : ((Llvm.llvalue * Llvm.llvalue) list) ref = ref []

let clear_tables () =
  Hashtbl.clear entry_points;
  Hashtbl.clear token_names;
  all_tokens := []

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
  part len1 z

(* TODO: check that truncation is correctly applied! 
* *)                      
let build_truncate_extend (enc : encoded_value) (a : Type.t) =
  let a_payload_size = payload_size a in
  let a_attrib_bitlen = attrib_size a in
  let rec mk_payload p n =
    if n = 0 then [] else 
      match p with
        | [] -> Llvm.const_null (Llvm.i64_type context) :: (mk_payload [] (n-1)) 
        | x::xs -> x :: (mk_payload xs (n-1)) in
  let x_payload = mk_payload enc.payload a_payload_size in
  let x_attrib = 
    let enc_attrib_bitlen = Bitvector.length enc.attrib in
      if enc_attrib_bitlen = a_attrib_bitlen then
        enc.attrib
      else if enc_attrib_bitlen < a_attrib_bitlen then
        (let leading_zeros = Bitvector.null (a_attrib_bitlen - enc_attrib_bitlen) in
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
      | Var(_) | UnitW | ConstW(Some _, _) -> t
      | ConstW(None, c) -> 
          let alpha = Type.newty Type.Var in
            mkConstW (Some alpha) c
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
      | AppW({ desc=LetW(s, (x, y, t1)) }, t2) -> 
          let fvt2 = free_vars t2 in
          let x' = variant_var_avoid x fvt2 in
          let y' = variant_var_avoid y fvt2 in
          annotate_term (mkLetW s ((x', y'), mkAppW (subst (mkVar y') y (subst (mkVar x') x t1)) t2))
      | AppW(t1, t2) -> mkAppW (annotate_term t1) (annotate_term t2)
      | LambdaW((x, a), t1) -> mkLambdaW ((x, a), annotate_term t1)
      | TrW(t1) -> mkTrW (annotate_term t1)
      | FoldW((alpha, a), t1) -> mkFoldW (alpha, a) (annotate_term t1)
      | UnfoldW((alpha, a), t1) -> mkUnfoldW (alpha, a) (annotate_term t1)
      | LetBoxW(_, _) -> assert false 
      | HackU (_, _)|CopyU (_, _)|CaseU (_, _, _)|LetBoxU (_, _)
      | BoxTermU _| LambdaU (_, _)|AppU (_, _)|LetU (_, _)|PairU (_, _) -> assert false
  in
  (* Compile annotated term *)
  let rec build_annotatedterm (ctx: (string * encoded_value) list) (t: Term.t) 
        : encoded_value =
(*    print_string (Printing.string_of_termW t);
    print_string "\n";*)
    match t.Term.desc with
      | Var(x) -> 
          List.assoc x ctx
      | ConstW(Some a, Cmin) ->
          let ap = payload_size a in
          let msl = attrib_size a in
          let zero = Llvm.const_null (Llvm.i64_type context) in
          let rec mp n = if n = 0 then [] else zero::(mp (n-1)) in
            { payload = mp ap; attrib = Bitvector.null msl }
      | ConstW(Some a, Cintconst(i)) ->
          assert (Type.finddesc a = Type.NatW);
          let vali = Llvm.const_int (Llvm.i64_type context) i in
            {payload = [vali]; attrib = Bitvector.null 0;}
      | AppW({desc = ConstW(Some a, Cintprint)}, t1) ->
          begin
            match Type.finddesc a with
              | Type.FunW(a1, a2) -> 
                  begin
                    match Type.finddesc a1 with
                      | Type.NatW ->
                          begin
                            match build_annotatedterm ctx t1 with
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
                      | _ -> assert false
                  end
              | _ -> assert false
          end
      | AppW({desc = AppW({desc = ConstW(Some a, binop)}, t1)}, t2) 
          when (binop = Cintadd || binop = Cintsub || binop = Cintmul || binop = Cintdiv) ->
          begin
            match build_annotatedterm ctx t1, build_annotatedterm ctx t2 with
              | {payload = [x]; attrib = ax },  {payload = [y]; attrib = ay } when   
                  Bitvector.length ax = 0  && Bitvector.length ay = 0 ->
                  let res =
                    match binop with
                      | Cintadd -> Llvm.build_add x y "sum" builder 
                      | Cintsub -> Llvm.build_sub x y "sub" builder 
                      | Cintmul -> Llvm.build_mul x y "mul" builder 
                      | Cintdiv -> Llvm.build_sdiv x y "sdiv" builder 
                      | _ -> assert false
                  in
                    {payload = [res]; attrib = Bitvector.null 0}
              | _ -> assert false
          end
      | AppW({desc = AppW({desc = ConstW(Some a, Cinteq)}, t1)}, t2) ->
          begin
            match build_annotatedterm ctx t1, build_annotatedterm ctx t2 with
              | {payload = [x]; attrib = ax},  {payload = [y]; attrib = ay} when
                  Bitvector.length ax = 0  && Bitvector.length ay = 0 ->
                  let eq = Llvm.build_icmp Llvm.Icmp.Ne x y "eq" builder in
                    {payload = []; attrib = Bitvector.of_list [eq]}
              | _ -> assert false
          end
      | ConstW(Some a, Cprint(s)) ->
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
      | ConstW(None, _) -> assert false
      | UnitW ->
          {payload = []; attrib = Bitvector.null 0}
      | TypeAnnot({ desc = PairW(t1, t2) }, Some a) ->
          begin
            match Type.finddesc a with
              | Type.TensorW(a1, a2) ->
                  let t1enc = build_annotatedterm ctx t1 in
                  let t2enc = build_annotatedterm ctx t2 in
                  let ta = Bitvector.concat t1enc.attrib t2enc.attrib in
                    {payload = t1enc.payload @ t2enc.payload; attrib = ta}
              | _ -> assert false
          end
      | LetW({ desc = TypeAnnot(s, Some a) }, (x, y, t)) ->
          begin
            match Type.finddesc a with
              | Type.TensorW(ax, ay) ->
                  let senc = build_annotatedterm ctx s in
                  let len_sxp = payload_size ax in
                  let len_syp = payload_size ay in
                  let len_sxa = attrib_size ax in
                  let len_sya = attrib_size ay in
                    assert (List.length senc.payload = len_sxp + len_syp);
                    assert (Bitvector.length senc.attrib = len_sxa + len_sya);
                    let sxp, syp = part len_sxp senc.payload in
                    let sxa, sya = Bitvector.takedrop len_sxa senc.attrib in
                      assert (Bitvector.length sya = len_sya);
                      build_annotatedterm ((x, {payload = sxp; attrib = sxa }) :: 
                                           (y, {payload = syp; attrib = sya }) :: ctx)  t
              | _ -> assert false
          end
      | TypeAnnot({ desc = InW(2, i, t) }, Some a) ->
          let tenc = build_annotatedterm ctx t in
          let branch = Llvm.const_int (Llvm.integer_type context 1) i in
          let attrib_branch = Bitvector.concat tenc.attrib (Bitvector.of_list [branch]) in
          let denc = { payload = tenc.payload; attrib = attrib_branch} in
            build_truncate_extend denc a
      | CaseW({ desc = TypeAnnot(u, Some a) }, [(x, s); (y, t)]) -> 
          let uenc = build_annotatedterm ctx u in
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
            let senc = build_annotatedterm ((x, xenc) :: ctx) s in
            let _ = Llvm.build_br block_res builder in
            let block_end_s = Llvm.insertion_block builder in
              Llvm.position_at_end block_t builder;
              let tenc = build_annotatedterm ((y, yenc) :: ctx) t in
              let _ = Llvm.build_br block_res builder in
              let block_end_t = Llvm.insertion_block builder in
                assert ((Bitvector.length senc.attrib) = (Bitvector.length tenc.attrib));
                (* insert phi nodes in result *)
                Llvm.position_at_end block_res builder;
                let z_attrib = Bitvector.build_phi 
                                 (senc.attrib, block_end_s) 
                                 (tenc.attrib, block_end_t) 
                                 builder in
                let z_payload = 
                  List.map 
                    (fun (x,y) -> Llvm.build_phi [(x, block_end_s);
                                                  (y, block_end_t)] "z" builder)
                    (List.combine senc.payload tenc.payload) in
                  {payload = z_payload; attrib = z_attrib}
      | FoldW((alpha, a), t) ->
          (* - malloc deklarieren
           * - store aufrufen
           *)
          let tenc = build_annotatedterm ctx t in
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
            (List.combine (list_init len_p (fun i -> i)) tenc.payload) @
            (list_init len_a (fun i -> (len_p + i, Bitvector.extractvalue tenc.attrib i)))
(*            List.combine
              (list_init (len_p + len_a) (fun i -> i)) 
              (tenc.payload @ tenc.attrib)*)
          in
          let t_struct = 
            List.fold_right 
              (fun (i,v) s -> Llvm.build_insertvalue s v i "tstruct" builder) 
              struct_content 
              (Llvm.undef a_struct)
          in
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
              match build_annotatedterm ctx t with
                | {payload = [tptrint]; attrib = a } when Bitvector.length a = 0 ->
                    let tptr = Llvm.build_inttoptr tptrint (Llvm.pointer_type a_struct) "tptr" builder in
                    let tstruct = Llvm.build_load tptr "tstruct" builder in
                    ignore (Llvm.build_call free (Array.of_list [tptrint]) "" builder);
                    let pl = list_init len_p (fun i -> Llvm.build_extractvalue tstruct i "p" builder) in
                    let at = list_init len_a (fun i -> Llvm.build_extractvalue tstruct (len_p + i) "p" builder) in
                      {payload = pl; attrib = Bitvector.of_list at}
                | _ -> assert false
            end
      | TypeAnnot(t, _) ->
          build_annotatedterm ctx t
      | AppW({desc = LambdaW((x, a), t1)}, t2) ->
          let t2enc = build_annotatedterm ctx t2 in
            build_annotatedterm ((x, t2enc) :: ctx) t1
      | AppW({desc = AppW({desc = LambdaW((x, a), {desc = LambdaW((y, b), t1)})}, t2)}, t3) ->
          let t3enc = build_annotatedterm ctx t3 in
          let t2enc = build_annotatedterm ctx t2 in
            build_annotatedterm ((y,t3enc) :: (x, t2enc) :: ctx) t1
      | _ -> 
          Printf.printf "%s\n" (Printing.string_of_termW t);
          failwith "TODO"
  in
(*        
 | AppW of t * t                        (* s, t *)
 | LambdaW of (var * Type.t option) * t (* <x>s *)
 | TrW of t                             (* t *)
 | LetBoxW of t * (var * t)             (* s, <x>t *)
 *)    
  let t_annotated = mkTypeAnnot (freshen_type_vars (annotate_term t)) (Some a) in
 (*   Printf.printf "%s\n" (Printing.string_of_termW t_annotated); *)
  let _ = Typing.principal_typeW type_ctx t_annotated in    
    build_annotatedterm ctx t_annotated



let replace_in_token_names (oldv : Llvm.llvalue) (newv : Llvm.llvalue)  =
  let replace (token_name : encoded_value) =
    let payload = List.map (fun v -> if v == oldv then newv else v) token_name.payload in
    let attrib = Bitvector.replace_all_uses_within oldv newv token_name.attrib in
      { payload = payload; attrib = attrib } in
    (* TODO: inefficient *)
  let bindings = Hashtbl.fold (fun n token bdgs -> (n,token)::bdgs) token_names [] in
    Hashtbl.clear token_names;
    List.iter (fun (n, token) -> Hashtbl.add token_names n (replace token)) bindings

let allocate_tables (is : instruction list) =
  clear_tables();
  let build_dummy ty name builder = 
     let i0 = Llvm.build_alloca ty name builder in
     let dummy = Llvm.build_bitcast i0 ty name builder in
       all_tokens := (dummy, Llvm.const_null ty)::!all_tokens;
       dummy
     in 
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
                 let name = Printf.sprintf "pl.%i.%i" n m in
                 let t = Llvm.i64_type context in
                 let i = build_dummy t name builder in
                 i :: (mk_p (m-1)) in
             let xp = mk_p (payload_size a) in
             let xs = attrib_size a in
             let rec mk_a m = 
               if m = 0 then [] 
               else 
                 let name = Printf.sprintf "a.%i.%i" n m in
                 let t = Llvm.i1_type context in
                 let i = build_dummy t name builder in
                 i :: (mk_a (m-1)) in
             let xa = mk_a xs in
               Hashtbl.add token_names n { payload = xp; attrib = Bitvector.of_list xa }
    ) in
  let all_wires = Compile.wires is in
    List.iter 
      (fun w ->
         add_module w.src w.type_back;
         add_module w.dst w.type_forward;
    ) all_wires

let build_instruction (the_module : Llvm.llmodule) (i : instruction) : unit =
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
      List.iter 
        (fun (o, n) -> 
           Llvm.replace_all_uses_with o n;
           replace_in_token_names o n
        ) 
        (List.combine oldenc.payload newenc.payload);
      List.iter 
        (fun (o, n) -> 
           Llvm.replace_all_uses_with o n;
           replace_in_token_names o n
        ) (Bitvector.value_replacement oldenc.attrib newenc.attrib);
  in
  let connect2 block1 new1enc block2 new2enc dst =
    assert ((Bitvector.length new1enc.attrib) = (Bitvector.length new2enc.attrib));
(*    let newal = new1enc.attrib_bitlen in *)
    let dstblock = Hashtbl.find entry_points dst in
      position_at_start dstblock builder;
    let newp =
      List.map 
        (fun (n1, n2) -> Llvm.build_phi [(n1, block1); (n2, block2)] "xp" builder)
        (List.combine new1enc.payload new2enc.payload) in
    let newa = Bitvector.build_phi (new1enc.attrib, block1) (new2enc.attrib, block2) builder in
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
  match i with
   | Axiom(w1 (* [f] *), f) ->
       begin
         let x, sigma, v = "x", "sigma", "v" in
         let t = mkLetW (mkVar x) 
                   ((sigma, v), (mkPairW (mkVar sigma) 
                                   (mkAppW (let_tupleW sigma f) (mkVar v)))) in
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
                                   (mkPairW (let_tupleW sigma f) (mkVar v)))) in
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
  List.iter (build_instruction the_module) c.instructions;
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
  List.iter (fun (t, z) -> Llvm.replace_all_uses_with t z) !all_tokens


(* Must be applied to circuit of type [A] *)    
let llvm_circuit (c : Compile.circuit) = 
  let the_module = Llvm.create_module context "intml" in
  let void = Llvm.void_type context in
  let ft = Llvm.function_type void (Array.make 0 void) in
  let f = Llvm.declare_function "main" ft the_module in
  let entry = Llvm.append_block context "entry" f in
  let dummy = Llvm.append_block context "dummy" f in
    Llvm.position_at_end dummy builder;
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
    (* Llvm.dump_module the_module; *)
    the_module
