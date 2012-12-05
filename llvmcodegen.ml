open Term
open Compile

let context = Llvm.global_context ()
let builder = Llvm.builder context
  
let position_at_start block builder =
  let block_begin = Llvm.instr_begin block in
    Llvm.position_builder block_begin builder

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
    
(*
  type t = { 
    vector : Llvm.llvalue option;
    len : int
  }

  let struct_type len =
    Llvm.integer_type context len

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
      List.fold_right (fun v s ->
                         let s' = Llvm.build_shl s (Llvm.const_int (struct_type len) 1) "s1" builder in
                         let ve = Llvm.build_zext v (struct_type len) "ve" builder in
                           Llvm.build_or s' ve "s2" builder)
        (List.rev bl) s
 
  let concat b1 b2 = 
 match b1.vector, b2.vector with
    | v1, None -> b1
    | None, v2 -> b2
    | Some x, Some y -> 
        let ilen = Llvm.integer_type context (b1.len + b2.len) in
        let zh' = Llvm.build_zext x ilen "zhext" builder in
        let cl2 = Llvm.const_int ilen b2.len in
        let zh = Llvm.build_shl zh' cl2 "zh" builder in
        let zl =Llvm.build_zext y ilen "zl" builder in
          {vector = Some (Llvm.build_or zh zl "z" builder);
           len = b1.len + b2.len}

  let takedrop n b1 =
    if n = 0 then { vector = None; len = 0 } , b1 
    else if n = b1.len then b1, { vector = None; len = 0 } 
    else 
    match b1.vector with 
      | None -> assert false
      | Some z -> 
          let ixn = Llvm.integer_type context n in
          let ilen = Llvm.integer_type context b1.len in
          let x' = Llvm.build_lshr z (Llvm.const_int ilen (b1.len - n)) "xshr" builder in
          let h = Llvm.build_trunc x' ixn "x" builder in
          let t = Llvm.build_trunc z (Llvm.integer_type context (b1.len - n)) "y" builder in
              { vector = Some h; len = n },
              { vector = Some t; len = b1.len - n }

  let extractvalue b i =    
    match b.vector with
      | Some v -> 
          let x' = Llvm.build_lshr v (Llvm.const_int (Llvm.integer_type context b.len) (b.len - i - 1)) "xshr" builder in
          let h = Llvm.build_trunc x' (Llvm.i1_type context) "x" builder in
            h
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
 *)
end

type encoded_value = {
  payload : Llvm.llvalue list;
  attrib: Bitvector.t
}
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
              | ZeroW | OneW -> 0
              | Var(_) -> 1
              | NatW -> 1
              | TensorW(a1, a2) -> p_s a1 + (p_s a2)
              | SumW[a1; a2] -> (max (p_s a1) (p_s a2))
              | MuW _ -> 1
              | HashW _ -> 1
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

let packing_type (a: Type.t) : Llvm.lltype =
  let i1 = Llvm.i1_type context in
  let i64 = Llvm.i64_type context in
  let len_p = payload_size a in
  let len_a = attrib_size a in
  let struct_members = Array.append (Array.make len_p i64) (Array.make len_a i1) in
  let struct_type = Llvm.packed_struct_type context struct_members in
    struct_type 

let pack_encoded_value (enc: encoded_value) (a: Type.t): Llvm.llvalue =
  let len_p = payload_size a in
  let len_a = attrib_size a in
  let struct_type = packing_type a in
  let struct_content = 
    (List.combine (Listutil.init len_p (fun i -> i)) enc.payload) @
    (Listutil.init len_a (fun i -> (len_p + i, Bitvector.extractvalue enc.attrib i))) in
  let packed_enc = 
    List.fold_right 
      (fun (i,v) s -> Llvm.build_insertvalue s v i "packed" builder) 
      struct_content 
      (Llvm.undef struct_type) in
    packed_enc

let unpack_encoded_value (packed_enc: Llvm.llvalue) (a: Type.t) : encoded_value =      
  let len_p = payload_size a in
  let len_a = attrib_size a in
  let pl = Listutil.init len_p (fun i -> Llvm.build_extractvalue packed_enc i "p" builder) in
  let at = Listutil.init len_a (fun i -> Llvm.build_extractvalue packed_enc (len_p + i) "p" builder) in
    {payload = pl; attrib = Bitvector.of_list at}

(* TODO: 
 * - restrict wc so that this compilation is always ok. (remove functions)
 * *)                      
let build_term 
      (the_module : Llvm.llmodule)
      (ctx: (var * encoded_value) list) 
      (type_ctx: (var * Type.t) list) (t: Term.t) (a: Type.t)
      : encoded_value =
  (* Add type annotations in various places *)
  let rec annotate_term (t: Term.t) : Term.t =
    match t.desc with
      | ConstW(Cbot) -> 
          let alpha = Type.newty Type.Var in
            mkTypeAnnot (mkConstW Cbot) (Some alpha)
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
      | TypeAnnot({ desc = ConstW(Cbot) }, Some a) ->
          let func = Llvm.block_parent (Llvm.insertion_block builder) in
          let inf_loop = Llvm.append_block context "bot" func in 
          let _ = Llvm.build_br inf_loop builder in
          let _ = Llvm.position_at_end inf_loop builder in
          let _ = Llvm.build_br inf_loop builder in
          let dummy = Llvm.append_block context "dummy" func in 
          let _ = Llvm.position_at_end dummy builder in
            build_truncate_extend {payload = []; attrib = Bitvector.null 0;} a
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
          let malloctype = Llvm.function_type 
                             (Llvm.pointer_type (Llvm.i8_type context)) 
                             (Array.of_list [i64]) in
          let malloc = Llvm.declare_function "malloc" malloctype the_module in
          let mua = Type.newty (Type.MuW(alpha, a)) in
          let a_unfolded = Type.subst (fun beta -> if Type.equals beta alpha then mua else beta) a in
          let a_struct = packing_type a_unfolded in
          let tenc_packed = pack_encoded_value tenc a_unfolded in
          let mem_i8ptr = Llvm.build_call malloc (Array.of_list [Llvm.size_of a_struct]) 
                            "memi8" builder in
          let mem_a_struct_ptr = Llvm.build_bitcast mem_i8ptr (Llvm.pointer_type a_struct) 
                                   "memstruct" builder in
          ignore (Llvm.build_store tenc_packed mem_a_struct_ptr builder);
          let pl = Llvm.build_ptrtoint mem_a_struct_ptr i64 "memint" builder in
            {payload = [pl]; attrib = Bitvector.null 0}
      | UnfoldW((alpha, a), t) ->
          let i64 = Llvm.i64_type context in
          let freetype = Llvm.function_type (Llvm.void_type context) (Array.of_list [i64]) in
          let free = Llvm.declare_function "free" freetype the_module in
          let mua = Type.newty (Type.MuW(alpha, a)) in
          let a_unfolded = Type.subst (fun beta -> if Type.equals beta alpha then mua else beta) a in
          let a_struct = packing_type a_unfolded in
            begin
              match build_annotatedterm ctx t args with
                | {payload = [tptrint]; attrib = a } when Bitvector.length a = 0 ->
                    let tptr = Llvm.build_inttoptr tptrint (Llvm.pointer_type a_struct) "tptr" builder in
                    let tstruct = Llvm.build_load tptr "tstruct" builder in
                    ignore (Llvm.build_call free (Array.of_list [tptrint]) "" builder);
                    unpack_encoded_value tstruct a_unfolded                      
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

let build_ssa_blocks (the_module : Llvm.llmodule) (func : Llvm.llvalue) 
      (ssa_func : Ssa.func) : unit =
  let blocks = Hashtbl.create 10 in
  let phi_nodes = Hashtbl.create 10 in    
  let get_block name =
    try
      Hashtbl.find blocks name
    with Not_found ->
      let label = Printf.sprintf "L%i" name in
      let block = Llvm.append_block context label func in
        Hashtbl.add blocks name block;
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
  let entry_block = Llvm.append_block context "entry" func in
    let packed_arg = Llvm.param func 0 in      
    Llvm.set_value_name "packed_arg" packed_arg;
    Llvm.position_at_end entry_block builder;
    let arg = unpack_encoded_value packed_arg ssa_func.Ssa.argument_type in
    ignore (Llvm.build_br (get_block ssa_func.Ssa.entry_block) builder);
    connect_to entry_block arg ssa_func.Ssa.entry_block;
    (* build unconnected blocks *)
    let open Ssa in
    List.iter 
      (fun block ->
         match block with
           | Unreachable(src) -> 
               (*                       Printf.printf "%i --> \n" src.name; *)
               Llvm.position_at_end (get_block src.name) builder;
               let senc = Hashtbl.find phi_nodes src.name in
                 ignore (Llvm.build_br (get_block src.name) builder);
                 connect_to (get_block src.name) senc src.name
           | Direct(src, x, lets, body, dst) ->
               Llvm.position_at_end (get_block src.name) builder;
               let senc = Hashtbl.find phi_nodes src.name in
               let t = Ssa.reduce (mkLets lets body) in
               let ev = build_term the_module 
                          [(x, senc)] [(x, src.message_type)] t dst.message_type in
               let src_block = Llvm.insertion_block builder in
                 ignore (Llvm.build_br (get_block dst.name) builder);
                 connect_to src_block ev dst.name
           | Branch(src, x, lets, (s, (xl, bodyl, dst1), (xr, bodyr, dst2))) ->
               begin
                 let t = reduce (
                      mkLets lets ( mkCaseW s 
                                      [(xl, mkInlW bodyl) ;
                                       (xr, mkInrW bodyr) ])) in
                 let src_block = get_block src.name in
                   Llvm.position_at_end src_block builder;
                   let senc = Hashtbl.find phi_nodes src.name in
                   let tenc = build_term the_module [(x, senc)] [(x, src.message_type)] t
                                (Type.newty (Type.SumW[dst1.message_type; dst2.message_type])) in
                   let da, cond = Bitvector.takedrop (Bitvector.length tenc.attrib - 1) tenc.attrib in
                   let denc12 = { payload = tenc.payload; attrib = da } in
                   let denc1 = build_truncate_extend denc12 dst1.message_type in
                   let denc2 = build_truncate_extend denc12 dst2.message_type in
                   let cond' = Bitvector.extractvalue cond 0 in
                   let src_block = Llvm.insertion_block builder in
                     ignore (Llvm.build_cond_br cond' (get_block dst2.name) 
                               (get_block dst1.name) builder);
                     connect_to src_block denc1 dst1.name;
                     connect_to src_block denc2 dst2.name
               end
           | Return(src, x, lets, body, return_type) ->
               Llvm.position_at_end (get_block src.name) builder;
               let senc = Hashtbl.find phi_nodes src.name in
               let t = Ssa.reduce (mkLets lets body) in
               let ev = build_term the_module 
                          [(x, senc)] [(x, src.message_type)] t return_type in
(*               let pty = packing_type return_type in*)
               let pev = pack_encoded_value ev return_type in
                 ignore (Llvm.build_ret pev builder)
                   (* TODO: actual return *)
      )                         
      ssa_func.blocks

let build_body (the_module : Llvm.llmodule) func (c : circuit) =
  let ssa_func = Ssa.trace c in
    build_ssa_blocks the_module func ssa_func

(* Must be applied to circuit of type [A] *)    
let llvm_circuit (c : Compile.circuit) = 
  let the_module = Llvm.create_module context "intml" in
  let ssa_func = Ssa.trace c in
  let arg_ty = packing_type ssa_func.Ssa.argument_type in
  let ret_ty = packing_type ssa_func.Ssa.return_type in
  let ft = Llvm.function_type ret_ty (Array.make 1 arg_ty) in
  let func = Llvm.declare_function ssa_func.Ssa.func_name ft the_module in
    build_ssa_blocks the_module func ssa_func;
    (* make main function *)
    let void_ty = Llvm.void_type context in
    let main_ty = Llvm.function_type void_ty (Array.make 0 void_ty) in
    let main = Llvm.declare_function "main" main_ty the_module in
    let start_block = Llvm.append_block context "start" main in 
    let args = Array.of_list [Llvm.undef arg_ty] in
      Llvm.position_at_end start_block builder;
      ignore (Llvm.build_call func args "ret" builder);
      ignore (Llvm.build_ret_void builder);           
(*    Llvm.dump_module the_module; *)
    the_module
