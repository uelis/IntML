open Term
open Compile

module IntMap = Map.Make(
  struct
    type t = int
    let compare = compare
  end
)

type encoded_value = {
  payload : Llvm.llvalue list;
  attrib: Llvm.llvalue option;
  attrib_bitlen: int
}
  
let context = Llvm.global_context ()
let the_module = Llvm.create_module context "test"
let builder = Llvm.builder context

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

let rec payload_size (a: Type.t) : int = 
  let open Type in
    match finddesc a with
      | Link _ -> assert false
      | Var(_) | ZeroW | OneW -> 0
      | NatW -> 1
      | TensorW(a1, a2) -> payload_size a1 + (payload_size a2)
      | SumW[a1; a2] -> (max (payload_size a1) (payload_size a2))
      | ListW _ -> failwith "TODO"
      | FunW(_, _) | BoxU(_, _) | TensorU(_, _) | FunU(_, _, _) | SumW _ -> assert false

let rec attrib_size (a: Type.t) : int = 
  let open Type in
    match finddesc a with
      | Link _ -> assert false
      | Var | ZeroW | OneW | NatW -> 0
      | TensorW(a1, a2) -> attrib_size a1 + (attrib_size a2)
      | SumW[a1; a2] -> 1 + (max (attrib_size a1) (attrib_size a2))
      | ListW _ -> failwith "TODO"
      | FunW(_, _) | BoxU(_, _) | TensorU(_, _) | FunU(_, _, _) | SumW _ -> assert false

let build_concat 
      (v1 : Llvm.llvalue option) (l1 : int) 
      (v2 : Llvm.llvalue option) (l2 : int) : Llvm.llvalue option =
  match v1, v2 with
    | v1, None -> v1
    | None, v2 -> v2
    | Some x, Some y -> 
        let ilen = Llvm.integer_type context (l1 + l2) in
        let zh' = Llvm.build_zext x ilen "zhext" builder in
        let cl2 = Llvm.const_int ilen l2 in
        let zh = Llvm.build_shl zh' cl2 "zh" builder in
        let zl =Llvm.build_zext y ilen "zl" builder in
          Some (Llvm.build_or zh zl "z" builder)

let build_split (z : Llvm.llvalue option) (len1 : int) (len2 : int) 
      : Llvm.llvalue option * Llvm.llvalue option =
  if len1 = 0 then None, z 
  else if len2 = 0 then z, None
  else 
    match z with 
      | None -> assert false
      | Some z -> 
          let ilen = Llvm.integer_type context (len1 + len2) in
          let ilen1 = Llvm.integer_type context len1 in
          let ilen2 = Llvm.integer_type context len2 in
          let x' = Llvm.build_lshr z (Llvm.const_int ilen len2) "xshr" builder in
          let x = Llvm.build_trunc x' ilen1 "x" builder in
          let y = Llvm.build_trunc z ilen2 "y" builder in
            Some x, Some y                      

(* TODO: doc 
* truncate if necessary
* *)                      
let build_truncate_extend (enc : encoded_value) (a : Type.t) =
  let a_payload_size = payload_size a in
  let a_attrib_bitlen = attrib_size a in
  let rec mk_payload p n =
    if n = 0 then [] else 
      match p with
        | [] -> Llvm.const_null (Llvm.i32_type context) :: (mk_payload [] (n-1)) 
        | x::xs -> x :: (mk_payload xs (n-1)) in
  let x_payload = mk_payload enc.payload a_payload_size in
  let x_attrib = 
    if enc.attrib_bitlen < a_attrib_bitlen then
      begin
        let i_a_attrib_bitlen = Llvm.integer_type context a_attrib_bitlen in
        match enc.attrib with
          | None -> 
              Some (Llvm.const_null i_a_attrib_bitlen)
          | Some enc_attrib' ->
              Some (Llvm.build_zext enc_attrib' i_a_attrib_bitlen
                      "zext_attrib" builder)
      end
    else if enc.attrib_bitlen > a_attrib_bitlen then
      begin
        assert (enc.attrib_bitlen > 0);
        match enc.attrib with
          | None -> assert false (* not possible if enc.attrib_bitlen > 0 *)
          | Some enc_attrib' ->
              if a_attrib_bitlen = 0 then None else
              Some (Llvm.build_trunc enc_attrib'
                      (Llvm.integer_type context a_attrib_bitlen) 
                      "trunc_attrib" builder)
      end 
    else
      (* nothing to truncate or extend *)
      enc.attrib
  in
    {payload = x_payload; attrib = x_attrib; attrib_bitlen = a_attrib_bitlen}

(*
 * Füge TypeAnnot an den Stellen ein, an denen Typinformationen
 * gebraucht werden.
 *
 * (Besser in dieser Funktion selbst auffrischen!?!) *)
let build_term (ctx: (var * encoded_value) list) 
      (type_ctx: (var * Type.t) list) (t: Term.t) (a: Type.t)
      : encoded_value =
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
      | LetBoxW(_, _) -> assert false 
      | HackU (_, _)|CopyU (_, _)|CaseU (_, _, _)|LetBoxU (_, _)
      | BoxTermU _| LambdaU (_, _)|AppU (_, _)|LetU (_, _)|PairU (_, _) -> assert false
  in
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
          let zero = Llvm.const_null (Llvm.i32_type context) in
          let rec mp n = if n = 0 then [] else zero::(mp (n-1)) in
          let ms = 
            if msl = 0 then None else 
              Some (Llvm.const_null (Llvm.integer_type context msl)) in
            {payload = mp ap; attrib = ms; attrib_bitlen = msl}
(*      | ConstW(Some a, Cmin) when Type.finddesc a = Type.NatW ->
          let i32 = Llvm.integer_type context 32 in
          let zero = Llvm.const_null i32 in
            [zero], None, 0*)
      | AppW({desc = ConstW(Some a, Csucc)}, t1) ->
          begin
            match Type.finddesc a with
              | Type.FunW(a1, a2) -> 
                  begin
                    match Type.finddesc a1 with
                      | Type.NatW ->
                          begin
                            match build_annotatedterm ctx t1 with
                              | {payload = [x]; attrib = None} -> 
                                  let one = Llvm.const_int (Llvm.i32_type context) 1 in
                                  let x' = Llvm.build_add x one "succ" builder in
                                    {payload = [x']; attrib = None; attrib_bitlen = 0}
                              | _ -> assert false
                          end
                      | _ -> assert false
                  end
              | _ -> assert false
          end
      | ConstW(Some a, Cprint(s)) ->
          let i32 = Llvm.i32_type context in
          let str = Llvm.build_global_string s "s" builder in            
          let strptr = Llvm.build_in_bounds_gep str (Array.make 2 (Llvm.const_null i32)) "strptr" builder in
            (* declare puts *)
          let i8a = Llvm.pointer_type (Llvm.i8_type context) in
          let putstype = Llvm.function_type (Llvm.i32_type context) (Array.make 1 i8a) in
          let puts = Llvm.declare_function "puts" putstype the_module in
          let args = Array.make 1 strptr in
            ignore (Llvm.build_call puts args "i" builder);
            {payload = []; attrib = None; attrib_bitlen = 0}
      | ConstW(None, _) -> assert false
      (* TODO  | ConstW of (Type.t option) * term_const *)
      | UnitW ->
          {payload = []; attrib = None; attrib_bitlen = 0}
      | TypeAnnot({ desc = PairW(t1, t2) }, Some a) ->
          begin
            match Type.finddesc a with
              | Type.TensorW(a1, a2) ->
                  let t1enc = build_annotatedterm ctx t1 in
                  let t2enc = build_annotatedterm ctx t2 in
                  let len_t1a = attrib_size a1 in
                  let len_t2a = attrib_size a2 in
                  let len = len_t1a + len_t2a in
                  let ta = build_concat (t1enc.attrib) len_t1a (t2enc.attrib) len_t2a in
                    {payload = t1enc.payload @ t2enc.payload; attrib = ta; attrib_bitlen = len}
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
                    assert (senc.attrib_bitlen = len_sxa + len_sya);
                    let sxp, syp = part len_sxp senc.payload in
                    let sxa, sya = build_split senc.attrib len_sxa len_sya in
                      build_annotatedterm ((x, {payload = sxp; attrib = sxa; attrib_bitlen = len_sxa}) :: 
                                           (y, {payload = syp; attrib = sya; attrib_bitlen = len_sya}) :: ctx)  t
              | _ -> assert false
          end
      | TypeAnnot({ desc = InW(2, i, t) }, Some a) ->
          let tenc = build_annotatedterm ctx t in
          let branch = Llvm.const_int (Llvm.integer_type context 1) i in
          let attrib_branch = build_concat tenc.attrib tenc.attrib_bitlen (Some branch) 1 in
          let denc = { payload = tenc.payload; attrib = attrib_branch; attrib_bitlen = tenc.attrib_bitlen + 1} in
            build_truncate_extend denc a
      | CaseW({ desc = TypeAnnot(u, Some a) }, [(x, s); (y, t)]) -> 
          let uenc = build_annotatedterm ctx u in
          let ax, ay = 
            match Type.finddesc a with
              | Type.SumW [ax; ay] -> ax, ay
              | _ -> assert false in
          assert (uenc.attrib_bitlen > 0);
          let xya, cond = build_split uenc.attrib (uenc.attrib_bitlen - 1) 1 in
          let xyenc = {payload = uenc.payload; attrib = xya; attrib_bitlen = uenc.attrib_bitlen - 1} in
          let xenc = build_truncate_extend xyenc ax in
          let yenc = build_truncate_extend xyenc ay in
          let func = Llvm.block_parent (Llvm.insertion_block builder) in
          let block_s = Llvm.append_block context "case_l" func in 
          let block_t = Llvm.append_block context "case_r" func in 
          let block_res = Llvm.append_block context "case_res" func in
            begin
            match cond with
              | None -> assert false
              | Some cond' ->
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
                      assert (senc.attrib_bitlen = tenc.attrib_bitlen);
                      (* insert phi nodes in result *)
                      Llvm.position_at_end block_res builder;
                      let z_attrib =
                        match senc.attrib, tenc.attrib with
                          | None, None -> None
                          | Some sa', Some ta' -> 
                              Some (Llvm.build_phi [(sa', block_end_s); 
                                                    (ta', block_end_t)] "za" builder)
                          | _, _ -> assert false in
                      let z_payload = 
                        List.map 
                          (fun (x,y) -> Llvm.build_phi [(x, block_end_s);
                                                        (y, block_end_t)] "z" builder)
                          (List.combine senc.payload tenc.payload) in
                        {payload = z_payload; attrib = z_attrib; attrib_bitlen = senc.attrib_bitlen}
            end
      | TypeAnnot(t, _) ->
          build_annotatedterm ctx t
      | AppW({desc = LambdaW((x, a), t1)}, t2) ->
          let t2enc = build_annotatedterm ctx t2 in
            build_annotatedterm ((x, t2enc) :: ctx) t1
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


let entry_points : (int, Llvm.llbasicblock) Hashtbl.t = Hashtbl.create 10                                                         
let token_names : (int, encoded_value) Hashtbl.t = Hashtbl.create 10
let all_tokens : ((Llvm.llvalue * Llvm.llvalue) list) ref = ref []

let replace_in_token_names (oldv : Llvm.llvalue) (newv : Llvm.llvalue)  =
  let replace (token_name : encoded_value) =
    let payload = List.map (fun v -> if v == oldv then newv else v) token_name.payload in
    let attrib = 
      match token_name.attrib with
        | None -> None
        | Some v -> if v == oldv then Some newv else token_name.attrib in
      {payload = payload; attrib = attrib; attrib_bitlen = token_name.attrib_bitlen } in
    (* TODO: inefficient *)
  let bindings = Hashtbl.fold (fun n token bdgs -> (n,token)::bdgs) token_names [] in
    Hashtbl.clear token_names;
    List.iter (fun (n, token) -> Hashtbl.add token_names n (replace token)) bindings

let allocate_tables (is : instruction list) =
  Hashtbl.clear entry_points;
  Hashtbl.clear token_names;
  all_tokens := [];
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
             let rec mk_p m = 
               if m = 0 then [] 
               else 
                 let name = Printf.sprintf "pl.%i.%i" n m in
                 let t = (Llvm.integer_type context 32) in
                 let i = build_dummy t name builder in
                 i :: (mk_p (m-1)) in
             let xp = mk_p (payload_size a) in
             let xs = attrib_size a in
(*               Printf.printf "%i %s %i\n" n (Printing.string_of_type a) xs;*)
               let token_name = Printf.sprintf "token%i" n in
             let xa = 
               if xs = 0 then None else 
                 let t = (Llvm.integer_type context xs) in
                 let i = build_dummy t token_name builder in
               Some i
                 (* (Llvm.declare_global (Llvm.integer_type context xs)
                  * token_name the_module) *)
             in 
               Hashtbl.add token_names n {payload = xp; attrib = xa; attrib_bitlen = xs}
    ) in
  let all_wires = Compile.wires is in
    List.iter 
      (fun w ->
         add_module w.src w.type_back;
         add_module w.dst w.type_forward;
    ) all_wires

let build_defining_instruction_map (is : Compile.instruction list) =
  let rec build_map i =
    match i with
      | [] -> IntMap.empty
      | node :: rest -> 
          List.fold_right 
            (fun w map -> IntMap.add w.src node map) 
            (Compile.wires [node]) (build_map rest) 
  in
    build_map is 

let build_instruction (i : instruction) : unit =
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
      assert (oldenc.attrib_bitlen = newenc.attrib_bitlen);
      assert (List.length oldenc.payload = (List.length newenc.payload));
      Hashtbl.replace token_names dst newenc;
      List.iter 
        (fun (n, o) -> 
           Llvm.replace_all_uses_with o n;
           replace_in_token_names o n
        ) 
        (List.combine newenc.payload oldenc.payload);
      (match newenc.attrib, oldenc.attrib with          
        | None, None -> ()
        | Some n, Some o -> 
            Llvm.replace_all_uses_with o n;
            replace_in_token_names o n
        | _ , _ -> assert false);
  in
  let connect2 block1 new1enc block2 new2enc dst =
    assert (new1enc.attrib_bitlen = new2enc.attrib_bitlen);
    let newal = new1enc.attrib_bitlen in
    let dstblock = Hashtbl.find entry_points dst in
      position_at_start dstblock builder;
    let newp =
      List.map 
        (fun (n1, n2) -> Llvm.build_phi [(n1, block1); (n2, block2)] "xp" builder)
        (List.combine new1enc.payload new2enc.payload) in
    let newa =
      match new1enc.attrib, new2enc.attrib with
        | None, None -> None
        | Some n1, Some n2 -> 
            Some (Llvm.build_phi [(n1, block1); (n2, block2)] "xa" builder)
        | _ , _ -> assert false in
      connect1 {payload = newp; attrib = newa; attrib_bitlen = newal} dst in
  let build_jump_argument w1 (x, t) w2 =
    let src_block = Hashtbl.find entry_points w1.src in
      Llvm.position_at_end src_block builder;
      let senc = Hashtbl.find token_names w1.src in
      build_term [(x, senc)] [(x, w1.type_back)] t w2.type_forward in
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
       let denc1' =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), (mkPairW (mkVar sigma) (mkInlW (mkVar v)))) in
            build_jump_argument w1 (x, t) w3 in
       let denc1 = build_truncate_extend denc1' w3.type_forward in
       (* <sigma, v> @ w2       |-->  <sigma, inr(v)> @ w3 *)
       let src2 = Hashtbl.find entry_points w2.src in
       let denc2' =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), (mkPairW (mkVar sigma) (mkInrW (mkVar v)))) in
            build_jump_argument w2 (x, t) w3 in
       let denc2 = build_truncate_extend denc2' w3.type_forward in
       (* insert phi *)         
       connect2 src1 denc1 src2 denc2 w3.dst;
       Llvm.position_at_end src1 builder;
       ignore (build_br w3.dst);
       Llvm.position_at_end src2 builder;
       ignore (build_br w3.dst);
       (* <sigma, inl(v)> @ w3  |-->  <sigma, v> @ w1
          <sigma, inr(v)> @ w3  |-->  <sigma, v> @ w2 *)        
       begin
         let src3 = Hashtbl.find entry_points w3.src in
           Llvm.position_at_end src3 builder;
           let senc = Hashtbl.find token_names w3.src in
           let d_payload = senc.payload in
           assert (senc.attrib_bitlen > 0);
           let d_attrib_bitlen = senc.attrib_bitlen - 1 in
           let d_attrib, cond = build_split senc.attrib d_attrib_bitlen 1 in
           let denc = {payload = d_payload; attrib = d_attrib; attrib_bitlen = d_attrib_bitlen} in
           let denc1 = build_truncate_extend denc w1.type_forward in
           let denc2 = build_truncate_extend denc w2.type_forward in
             match cond with
               | None -> assert false
               | Some cond' ->
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
         let a, b  = 
           match Type.finddesc w1.type_back, 
                 Type.finddesc w2.type_forward with 
             | Type.TensorW(a, _), Type.TensorW(b, _) -> a, b
             | _ -> assert false in
         let t = mkLetW (mkVar x) 
                   ((sigma, y), mkLetW (mkVar y) 
                                  ((c, v), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkAppW (project b a) (mkVar c)) 
                                                 (mkVar v))))) in
            build_jwa w1 (x, t) w2
       end;
       begin
         let a, b  = 
           match Type.finddesc w1.type_forward, 
                 Type.finddesc w2.type_back with 
             | Type.TensorW(a, _), Type.TensorW(b, _) -> a, b
             | _ -> assert false in
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
       let denc2' =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), mkLetW (mkVar v) 
                                  ((d, y), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkInlW (mkVar d)) (mkVar y))))) in
            build_jump_argument w2 (x, t) w1 in
         (*unnötig?*)
       let denc2 = build_truncate_extend denc2' w1.type_forward in
       (* <sigma, <v,w>> @ w3         |-->  <sigma, <inr(v),w>> @ w1 *)
       let src3 = Hashtbl.find entry_points w3.src in
       let denc3' =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), mkLetW (mkVar v) 
                                  ((d, y), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkInrW (mkVar d)) (mkVar y))))) in
            build_jump_argument w3 (x, t) w1 in
       let denc3 = build_truncate_extend denc3' w1.type_forward in
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
           let tenc = build_term [(x, senc)] [(x, w1.type_back)] t 
                        (Type.newty (Type.SumW[w2.type_forward; w3.type_forward])) in
           let dal = tenc.attrib_bitlen - 1 in
           let da, cond = build_split tenc.attrib dal 1 in
           let denc23 = {payload = tenc.payload; attrib = da; attrib_bitlen = dal }in
           let denc2 = build_truncate_extend denc23 w2.type_forward in
           let denc3 = build_truncate_extend denc23 w3.type_forward in
             match cond with
               | None -> assert false
               | Some cond' ->
                   connect1 denc2 w2.dst;
                   connect1 denc3 w3.dst;
                   ignore (build_cond_br cond' w3.dst w2.dst)
       end         

let build_body (c : circuit) =
  List.iter build_instruction c.instructions;
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
    build_body c;
    Llvm.delete_block dummy; 
    Llvm.dump_module the_module;
    the_module
