open Term
open Compile

module IntMap = Map.Make(
  struct
    type t = int
    let compare = compare
  end
)

type encoded_value = Llvm.llvalue list * (Llvm.llvalue option) * int
  
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
            mkTypeAnnot 
              (mkCaseW (annotate_term t1) [(x, annotate_term t2); (y, annotate_term t3)])
              (Some alpha)
      | CaseW(_, _) -> assert false
      | AppW({ desc=LetW(s, (x, y, t1)) }, t2) -> 
          (* TODO: binding *)
          annotate_term (mkLetW s ((x, y), mkAppW t1 t2))
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
            mp ap, ms, msl
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
                              | [x], None, 0 -> 
                                  let i32 = Llvm.integer_type context 32 in
                                  let one = Llvm.const_int i32 1 in
                                  let x' = Llvm.build_add x one "succ" builder in
                                    [x'], None, 0
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
            [], None, 0
      | ConstW(None, _) -> assert false
      (* TODO  | ConstW of (Type.t option) * term_const *)
      | UnitW ->
          [], None, 0
      | TypeAnnot({ desc = PairW(t1, t2) }, Some a) ->
          begin
            match Type.finddesc a with
              | Type.TensorW(a1, a2) ->
                  let t1p, t1a, t1al = build_annotatedterm ctx t1 in
                  let t2p, t2a, t2al = build_annotatedterm ctx t2 in
                  let len_t1a = attrib_size a1 in
                  let len_t2a = attrib_size a2 in
                  let len = len_t1a + len_t2a in
                  let ta = build_concat t1a len_t1a t2a len_t2a in
                    t1p @ t1p, ta, len
              | _ -> assert false
          end
      | LetW({ desc = TypeAnnot(s, Some a) }, (x, y, t)) ->
          begin
            match Type.finddesc a with
              | Type.TensorW(ax, ay) ->
                  let sp, sa, sal = build_annotatedterm ctx s in
                  let len_sxp = payload_size ax in
                  let len_syp = payload_size ay in
                  let len_sxa = attrib_size ax in
                  let len_sya = attrib_size ay in
                    assert (List.length sp = len_sxp + len_syp);
                    assert (sal = len_sxa + len_sya);
                    let sxp, syp = part len_sxp sp in
                    let sxa, sya = build_split sa len_sxa len_sya in
                      build_annotatedterm ((x, (sxp, sxa, len_sxa)) :: 
                                           (y, (syp, sya, len_sya)) :: ctx)  t
              | _ -> assert false
          end
      | TypeAnnot({ desc = InW(2, i, t) }, Some a) ->
          let tp, ta, tal = build_annotatedterm ctx t in
          let i1 = Llvm.integer_type context 1 in
          let branch = 
            if i = 0 then Llvm.const_null i1 
            else if i = 1 then Llvm.const_all_ones i1 
            else assert false in
          let tao = build_concat ta tal (Some branch) 1 in
          let rec fill_payload n xp =
            if n = 0 then xp else 
              fill_payload (n-1) (xp @ [Llvm.const_null (Llvm.i32_type context)]) in
          let xp = fill_payload (payload_size a - (List.length tp)) tp in
          let xal = attrib_size a in
          let xa = 
            if (attrib_size a) > tal then
              match tao with
                | Some tao' ->
                    Some (Llvm.build_zext tao'
                            (Llvm.integer_type context xal) 
                            "xa" builder)
                | None -> assert false
            else 
              tao in
            xp, xa, xal
      | TypeAnnot({ desc = CaseW(u, [(x, s); (y, t)]) }, Some a) -> 
          let func = Llvm.block_parent (Llvm.insertion_block builder) in
          let block_s = Llvm.append_block context "case_l" func in 
          let block_t = Llvm.append_block context "case_r" func in 
          let block_res = Llvm.append_block context "case_res" func in
          let up, ua, ual = build_annotatedterm ctx u in
          let ax, ay = 
            match Type.finddesc a with
              | Type.SumW [ax; ay] -> ax, ay
              | _ -> assert false in
          let xp, _ = part (payload_size ax) up in
          let yp, _ = part (payload_size ay) up in
          let xal = attrib_size ax in
          let yal = attrib_size ay in
          let xya, cond = build_split ua (ual - 1) 1 in
          let xa = 
            if xal < ual - 1 then
              match xya with
                | Some xya' ->
                    Some (Llvm.build_trunc xya' (Llvm.integer_type context xal) "xa" builder)
                | None -> assert false (* not possible if xal < ual -1 *)
            else
              xya in
          let ya = 
            if yal < ual -1 then
              match xya with
                | Some xya' ->
                    Some (Llvm.build_trunc xya' (Llvm.integer_type context yal) "ya" builder)
                | None -> assert false (* not possible if xal < ual -1 *)
            else
              xya in
            assert (ual > 0);
            begin
              match cond with
                | None -> assert false
                | Some cond' ->
                    ignore (Llvm.build_cond_br cond' block_s block_t builder);
                    Llvm.position_at_end block_s builder;
                    let sp, sa, sal = build_annotatedterm ((x, (xp, xa, xal)) :: ctx) s in
                      ignore (Llvm.build_br block_res builder);
                      Llvm.position_at_end block_t builder;
                      let tp, ta, tal = build_annotatedterm ((y, (yp, ya, yal)) :: ctx) t in
                        ignore (Llvm.build_br block_res builder);
                        assert (sal = tal);
                        (* insert phi nodes in result *)
                        Llvm.position_at_end block_res builder;
                        let za =
                          match sa, ta with
                            | None, None -> None
                            | Some sa', Some ta' -> 
                                Some (Llvm.build_phi [(sa', block_s); 
                                                      (ta', block_t)] "za" builder)
                            | _, _ -> assert false in
                        let zp = 
                          List.map 
                            (fun (x,y) -> Llvm.build_phi [(x, block_s);
                                                          (y, block_t)] "z" builder)
                            (List.combine sp tp) in
                          zp, za, sal
            end
      | TypeAnnot(t, _) ->
          build_annotatedterm ctx t
      | AppW({desc = LambdaW((x, a), t1)}, t2) ->
          let t2p, t2a, t2al = build_annotatedterm ctx t2 in
            build_annotatedterm ((x, (t2p, t2a, t2al)) :: ctx) t1
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

let allocate_tables (is : instruction list) =
  Hashtbl.clear entry_points;
  let build_dummy ty name builder = 
     let i0 = Llvm.build_alloca ty name builder in
       Llvm.build_bitcast i0 ty name builder in 
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
               Hashtbl.add token_names n (xp, xa, xs)
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
  let build_br xp xa xal dst = 
    let dst_block = Hashtbl.find entry_points dst in
      Llvm.build_br dst_block builder in    
  let build_cond_br xp xa xal cond tdst fdst= 
    let tdst_block = Hashtbl.find entry_points tdst in
    let fdst_block = Hashtbl.find entry_points fdst in
      Llvm.build_cond_br cond tdst_block fdst_block builder in
    (* w1 and w2 are attached with src to same node. Message arrives on w1,
     * is passed to w2 *)
  let connect1 (newp, newa, newal) dst =
    let oldp, olda, oldal = Hashtbl.find token_names dst in
(*         Printf.printf "%i %i -> %i\n" oldal newal dst;*)
      assert (oldal <= newal);
      List.iter 
        (fun (n, o) -> Llvm.replace_all_uses_with o n) 
        (List.combine newp oldp);
      let newa =
        match newa, olda with          
          | None, None | Some _, None -> None
          | Some n, Some o -> 
              let n' =
                if newal > oldal then
                  Llvm.build_trunc n (Llvm.integer_type context oldal) "xa" builder 
                else n in
                Llvm.replace_all_uses_with o n';
                Some n'
          | _ , _ -> assert false
      in
      Hashtbl.replace token_names dst (newp, newa, oldal)
  in
  let connect2 (block1, new1p, new1a, new1al) (block2, new2p, new2a, new2al) dst =
    let newal = max new1al new2al in
    let extend na nl block =
      Llvm.position_at_end block builder;
      if newal > nl then
        begin
        match na with
          | None -> 
              Some (Llvm.const_null (Llvm.integer_type context newal))
          | Some n1 ->
              (Some (Llvm.build_zext n1 (Llvm.integer_type context newal) "xa" builder))
        end
      else na in
    let new1a = extend new1a new1al block1 in
    let new2a = extend new2a new2al block2 in
    let dstblock = Hashtbl.find entry_points dst in
      position_at_start dstblock builder;
    let newp =
      List.map 
        (fun (n1, n2) -> Llvm.build_phi [(n1, block1); (n2, block2)] "xp" builder)
        (List.combine new1p new2p) in
    let newa =
      match new1a, new2a with
        | None, None -> None
        | Some n1, Some n2 -> 
            Some (Llvm.build_phi [(n1, block1); (n2, block2)] "xa" builder)
              (* TODO *)
        | _ , _ -> assert false in
      connect1 (newp, newa, newal) dst in
  let build_jump_argument w1 (x, t) w2 =
    let src_block = Hashtbl.find entry_points w1.src in
      Llvm.position_at_end src_block builder;
      let sp, sa, sal = Hashtbl.find token_names w1.src in
      build_term [(x, (sp, sa, sal))] [(x, w1.type_back)] t w2.type_forward in
  (* build actual jump with argument *)
  let build_jwa w1 (x, t) w2 =
    let dp, da, dal = build_jump_argument w1 (x, t) w2 in
      ignore (build_br dp da dal w2.dst);
      connect1 (dp, da, dal) w2.dst
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
       (* <sigma, v> @ w1       |-->  <sigma, inl(v)> @ w3 *)
       let src1, dp1, da1, dal1 =
         let src1 = Hashtbl.find entry_points w1.src in
           Llvm.position_at_end src1 builder;
           let sp, sa, sal = Hashtbl.find token_names w1.src in
           let i1 = Llvm.integer_type context 1 in
           let zero = Llvm.const_null i1 in
           let dp = sp in
           let da = build_concat sa sal (Some zero) 1 in
           let dal = sal + 1 in
             src1, dp, da, dal
       in
       (* <sigma, v> @ w2       |-->  <sigma, inr(v)> @ w3 *)
       let src2, dp2, da2, dal2 =
         let src2 = Hashtbl.find entry_points w2.src in
           Llvm.position_at_end src2 builder;
           let sp, sa, sal = Hashtbl.find token_names w2.src in
           let i1 = Llvm.integer_type context 1 in
           let one = Llvm.const_all_ones i1 in
           let dp = sp in
           let da = build_concat sa sal (Some one) 1 in
           let dal = sal + 1 in
             src2, dp, da, dal
       in
       (* insert phi *)
       connect2 (src1, dp1, da1, dal1) (src2, dp2, da2, dal2) w3.dst;
       Llvm.position_at_end src1 builder;
       ignore (build_br dp1 da1 dal1 w3.dst);
       Llvm.position_at_end src2 builder;
       ignore (build_br dp2 da2 dal2 w3.dst);
       (* <sigma, inl(v)> @ w3  |-->  <sigma, v> @ w1
          <sigma, inr(v)> @ w3  |-->  <sigma, v> @ w2 *)        
       begin
         let src3 = Hashtbl.find entry_points w3.src in
           Llvm.position_at_end src3 builder;
           let sp, sa, sal = Hashtbl.find token_names w3.src in
           let dp = sp in
           assert (sal > 0);
           let dal = sal - 1 in
           let da, cond = build_split sa dal 1 in
             match cond with
               | None -> assert false
               | Some cond' ->
                   connect1 (dp, da, dal) w1.dst;
                   connect1 (dp, da, dal) w2.dst;
                   ignore (build_cond_br dp da dal cond' w2.dst w1.dst);
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
        let a, b  = 
          match Type.finddesc w1.type_back, 
                Type.finddesc w2.type_forward with 
            | Type.TensorW(a, _), Type.TensorW(b, _) -> a, b
            | _ -> assert false in
       let x, sigma, v, y, c = "x", "sigma", "v", "y", "c" in
       begin
         let t = mkLetW (mkVar x) 
                   ((sigma, y), mkLetW (mkVar y) 
                                  ((c, v), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkAppW (project b a) (mkVar c)) 
                                                 (mkVar v))))) in
            build_jwa w1 (x, t) w2
       end;
       begin
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
       let dp2, da2, dal2 =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), mkLetW (mkVar v) 
                                  ((d, y), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkInlW (mkVar d)) (mkVar y))))) in
            build_jump_argument w2 (x, t) w1 in
       (* <sigma, <v,w>> @ w3         |-->  <sigma, <inr(v),w>> @ w1 *)
       let src3 = Hashtbl.find entry_points w3.src in
       let dp3, da3, dal3 =
         let t = mkLetW (mkVar x) 
                   ((sigma, v), mkLetW (mkVar v) 
                                  ((d, y), (mkPairW (mkVar sigma) 
                                              (mkPairW (mkInrW (mkVar d)) (mkVar y))))) in
            build_jump_argument w3 (x, t) w1 in
       connect2 (src2, dp2, da2, dal2) (src3, dp3, da3, dal3) w1.dst;
       Llvm.position_at_end src2 builder;
       ignore (build_br dp2 da2 dal2 w1.dst);
       Llvm.position_at_end src3 builder;
       ignore (build_br dp3 da3 dal3 w1.dst);

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
           let sp, sa, sal = Hashtbl.find token_names w1.src in
           let dp, dai, dali = build_term [(x, (sp, sa, sal))] [(x, w1.type_back)] t 
                               (Type.newty (Type.SumW[w2.type_forward; w3.type_forward])) in
           let dal = dali - 1 in
           let da, cond = build_split sa dal 1 in
             match cond with
               | None -> assert false
               | Some cond' ->
                   connect1 (dp, da, dal) w2.dst;
                   connect1 (dp, da, dal) w3.dst;
                   ignore (build_cond_br dp da dal cond' w3.dst w2.dst)
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
  ) entry_points

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
(*    Llvm.delete_block dummy; *)
    Llvm.dump_module the_module
