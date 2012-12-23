open Term
open Circuit

type label = { 
  name: int; 
  message_type: Type.t
}               
type let_bindings = (Term.t * (Term.var * Term.var)) list 
(* Branch must have at least two sucessors *)
type block = 
    Unreachable of label
  | Direct of label * Term.var * let_bindings * Term.t * label
  | InDirect of label * Term.var * let_bindings * Term.t * (label list) (* all destinations must accept the same message type *)
  | Branch of label * Term.var * let_bindings * (Type.Data.id * Term.t * (Term.var * Term.t * label) list)
  | Return of label * Term.var * let_bindings * Term.t * Type.t

type func = {
  func_name : string;
  argument_type: Type.t;
  entry_block : int;
  blocks : block list;
  return_type: Type.t;
}

let fresh_var = Vargen.mkVarGenerator "x" ~avoid:[]

let rec mkLets lets t =
  match lets with
    | [] -> t
    | (s, (x, y)) :: lets' -> mkLets lets' (mkLetW s ((x, y), t)) 

(* TODOTODO *)
let rec reduce (t : Term.t) : let_bindings * Term.t =
  match t.Term.desc with
    | Var(_) 
    | ConstW(Cundef) 
    | ConstW(Cintconst _) 
    | ConstW(Cintprint)
    | UnitW | LambdaW(_) 
    | AppW({desc=ConstW(Cintadd)}, _)
    | AppW({desc=ConstW(Cintsub)}, _)
    | AppW({desc=ConstW(Cintdiv)}, _)
    | AppW({desc=ConstW(Cintmul)}, _)
    | AppW({desc=ConstW(Cintslt)}, _)
    | AppW({desc=ConstW(Cinteq)}, _) -> [], t
    | ConstW(_) | LoopW(_) | AssignW _ | ContW _ | CallW _ -> 
        let x = fresh_var () in
        let y = fresh_var () in
          [(mkPairW t mkUnitW, (x, y))],
          mkVar x
    | TypeAnnot(t, a) ->
        let lets, t' = reduce t in
          lets, mkTypeAnnot t' a
    | InW(id, j, t) -> 
        let lets, t' = reduce t in
        let t'' = mkInW id j t' in
          (* Mutable types must not be reduced, as their value might change;
           * could make an exception for recursive types here. *)
          if Type.Data.is_mutable id then
            begin
              let x = fresh_var () in
              let y = fresh_var () in
                (mkPairW t'' mkUnitW, (x, y)) :: lets,
                mkVar x
            end 
          else
            lets, t''
    | PairW(t1, t2) ->
        let lets1, t1' = reduce t1 in
        let lets2, t2' = reduce t2 in
          lets2 @ lets1,
          mkPairW t1' t2'
    | LetW(t1, (x, y, t2)) ->
        let lets1, t1' = reduce t1 in
          begin
            match t1'.Term.desc with
              | PairW(s1, s2) ->
                  (* Need to be careful to avoid accidental capture. *)
                  let x' = fresh_var () in
                  let y' = fresh_var () in
                  let t' = Term.rename_vars (fun z -> if z = x then x' else if z = y then y' else z) t2 in
                  let lets2, t2' = reduce (Term.subst s1 x' (Term.subst s2 y' t')) in
                    lets2 @ lets1,
                    t2'
              | _ -> 
                  let lets2, t2' = reduce t2 in
                    lets2 @ ((t1', (x,y)) :: lets1), t2'
          end
    | CaseW(id, destruct, s, cases) ->
        let letss, rs = reduce s in
          begin
            match rs.Term.desc with
              | InW(id, i, rs0) ->
                  let u, su = List.nth cases i in
                  let letsu, ru = reduce (Term.subst rs0 u su) in
                    letsu @ letss, ru
              | _ ->
                  let reduced_cases =
                    List.fold_right (fun (u, su) reduced_cases ->
                                       let letsu, ru = reduce su in
                                         (u, mkLets letsu ru) :: reduced_cases)
                      cases [] in
                  let x = fresh_var () in
                  let y = fresh_var () in
                    (mkPairW (mkCaseW id destruct rs reduced_cases) mkUnitW, (x, y)) :: letss, 
                    mkVar x
          end
    | AppW(t1, t2) ->
        let lets1, rt1 = reduce t1 in
        let lets2, rt2 = reduce t2 in
          begin
            match rt1.Term.desc with
              | TypeAnnot({desc=LambdaW((x, a), f)}, _)  (* TODOTODO *)
              | LambdaW((x, a), f) ->
                  let lets3, rt = reduce (Term.subst rt2 x f) in
                    lets3 @ lets2 @ lets1, rt
              | _ -> 
                  let x = fresh_var () in
                  let y = fresh_var () in
                    (mkPairW (mkAppW rt1 rt2) mkUnitW, (x, y)) :: lets2 @ lets1, 
                    mkVar x
          end
    | _ -> 
        Printf.printf "%s\n" (Printing.string_of_termW t);
        failwith "TODO_ssa"

module IntMap = Map.Make(
  struct
    type t = int
    let compare = compare
  end
)

let trace (name: string) (c: Circuit.circuit) : func =
  (* Supply of fresh variable names. 
   * (The instructions do not contain a free variable starting with "x")
   *)
  let unTensorW a =
    match Type.finddesc a with
      | Type.TensorW(a1, a2) -> a1, a2
      | _ -> assert false in
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
  let possible_indirect_goals =
    let rec goals instructions =
      match instructions with
        | [] -> []
        | Grab(_, _, wt) :: rest -> { name = wt.dst; message_type = wt.type_forward } :: goals rest
        | Force(w, _) :: rest -> { name = w.dst; message_type = w.type_forward }  :: goals rest
        | _ :: rest -> goals rest in 
      goals instructions_fresh in
  let max_wire_src_dst = 
    List.fold_right (fun w m -> max w.src (max w.dst m)) 
      (wires instructions_fresh) 0 in
  let node_map_by_src = 
    let rec build_dst_map i =
      match i with
        | [] -> IntMap.empty
        | node :: rest -> 
            List.fold_right (fun w map -> IntMap.add w.src node map) 
              (wires [node]) (build_dst_map rest) 
    in build_dst_map instructions_fresh in
  let rec trace src dst lets (sigma, v) =
    let unpair t lets =
      match t.Term.desc with
        | PairW(x, y) -> (x, y), lets
        | _ -> 
            let x = fresh_var () in
            let y = fresh_var () in
              (mkVar x, mkVar y), (t, (x, y)) :: lets in
    (* TODO: do properly !! *)      
    let rec make_bindings t (vars, f) =
      match vars with 
        | [] -> [], t, f
        | x :: rest ->
            begin
              match t.Term.desc with
                | PairW(t', t2) -> 
                    let f' = Term.subst t2 x f in
                    let lets, t'', f'' = make_bindings t' (rest, f') in
                      lets, mkPairW t'' t2, f''
                | _ -> 
                    let th = fresh_var () in
                    let tr = fresh_var () in
                    let f' = Term.rename_vars (fun u -> if u = x then tr else u) f in
                    let lets, t', f'' = make_bindings (mkVar th) (rest, f') in
                      lets @ [(t, (th, tr))], mkPairW t' (mkVar tr), f'' 
            end in
      if not (IntMap.mem dst node_map_by_src) then
        begin
          if dst = c.output.dst then
            Return(src, "z", lets, mkPairW sigma v, c.output.type_forward) 
          else 
            (* unreachable *)
            Unreachable(src)
        end
      else 
        match IntMap.find dst node_map_by_src with
          | Axiom(w1 (* [f] *), f) when dst = w1.src ->
              let newlets, sigma', f' = make_bindings sigma f in
              let rlets, f'' = reduce (mkAppW f' v) in
                trace src w1.dst (rlets @ newlets @ lets) (sigma', f'')
(*              Direct(src, "z", newlets @ lets, mkPairW sigma' (mkAppW f' v), 
                         {name = w1.dst; message_type = w1.type_forward}) *)
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
                  | InW(id, 0, v') when id = Type.Data.sumid 2 -> 
                      trace src w1.dst lets (sigma, v')
                  | InW(id, 1, v') when id = Type.Data.sumid 2 -> 
                      trace src w2.dst lets (sigma, v')
                  | _ -> 
                      (* Printf.printf "%s\n" (Printing.string_of_termW v); *)
                      let v' = fresh_var () in 
                        (*                      assert (Type.equals src.message_type w3.type_back);*)
                        Branch(src, "z", lets,
                               (Type.Data.sumid 2, v, 
                                [(v', mkPairW sigma (mkVar v'), {name = w1.dst; message_type = w1.type_forward});
                                (v', mkPairW sigma (mkVar v'), {name = w2.dst; message_type = w2.type_forward})]))
              end
          | Der(w1 (* \Tens A X *), w2 (* X *), f) when dst = w1.src ->
              let rlets, v' = reduce (mkSndW v) in
              trace src w2.dst (rlets @ lets) (sigma, v')
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
                trace src w1.dst lets'' (sigma', mkPairW (mkPairW d c) v')
          | LWeak(w1 (* \Tens A X *), 
                  w2 (* \Tens B X *)) (* B <= A *) when dst = w1.src ->
              let _, a_token = unTensorW w1.type_back in
              let a, _ = unTensorW a_token in
              let _, b_token = unTensorW w2.type_forward in
              let b, _ = unTensorW b_token in
              let (c, v'), lets' = unpair v lets in
              let rlets, v'' = reduce (* (mkPairW c' v') *) (mkPairW (mkAppW (Typing.project b a) c) v') in
                trace src w2.dst (rlets @ lets') (sigma, v'')
          | LWeak(w1 (* \Tens A X *), 
                  w2 (* \Tens B X *)) (* B <= A *) when dst = w2.src ->
              let _, a_token = unTensorW w1.type_forward in
              let a, _ = unTensorW a_token in
              let _, b_token = unTensorW w2.type_back in
              let b, _ = unTensorW b_token in
              let (c, v'), lets' = unpair v lets in
              let rlets, v'' = reduce (* (mkPairW c' v') *) (mkPairW (mkAppW (Typing.embed b a) c) v') in
                trace src w1.dst (rlets @ lets') (sigma, v'')
          | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) when dst = w3.src ->
              (*   <sigma, *> @ w3      |-->  <sigma, *> @ w1 *)
              trace src w1.dst lets (sigma, mkUnitW)
          | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) when dst = w1.src ->
              (* <sigma, v> @ w1      |-->  <sigma, <v,*>> @ w2 *)
              trace src w2.dst lets (sigma, mkPairW v mkUnitW)
          | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) when dst = w2.src ->
              (* <sigma, <v,w>> @ w2  |-->  <sigma, w> @ w3 *)
              let rlets, v' = reduce (mkSndW v) in
              trace src w3.dst (rlets @ lets) (sigma, v')
          | Case(id, w1, ws) when List.mem dst (List.map (fun w -> w.src) ws) -> 
              (*  <sigma, <v,w>> @ w2         |-->  <sigma, <inl(v),w>> @ w1 *) 
                let n = List.length ws in
                let wsi = List.combine 
                            (List.map (fun w -> w.src) ws)
                            (Listutil.init n (fun i -> i)) in
                let i = List.assoc dst wsi in
              let (c, v'), lets' = unpair v lets in
                trace src w1.dst lets' (sigma, mkPairW (mkInW id i c) v')
          | Case(id, w1, ws) when dst = w1.src -> 
              (*   <sigma, <inl(v), w>> @ w1   |-->  <sigma, <v,w>> @ w2
               <sigma, <inr(v), w>> @ w1   |-->  <sigma, <v,w>> @ w3 *)
              begin
                let (c', v'), lets' = unpair v lets in
                  match c'.Term.desc with
                    | InW(id, i, c) -> 
                        trace src (List.nth ws i).dst lets' (sigma, mkPairW c v')
                    | _ ->
                        let c = fresh_var () in
                          (*                      assert (Type.equals src.message_type w1.type_back); *)
                          Branch(src, "z", lets', 
                                 (id, c', 
                                  List.map (fun w ->
                                               (c, mkPairW sigma (mkPairW (mkVar c) v'), 
                                                {name = w.dst; message_type = w.type_forward})) ws))
              end
           | Grab(s, w1, wt) when w1.src = dst ->
                trace src w1.dst lets
                   (sigma, mkContW wt.dst (max_wire_src_dst + 1) sigma)
           | Grab(_, w1, wt) when wt.src = dst ->
                InDirect(src, "z", lets, v, possible_indirect_goals)
           | External(fn, ty, w1) when w1.src = dst ->
                let ty' = Type.freshen ty in 
                let q, a = Type.question_answer_pair ty' in
                let s = Type.newty Type.Var in
                let sigmaq = Type.newty (Type.TensorW(s, q)) in
                let sigmaa = Type.newty (Type.TensorW(s, a)) in
                let rec pack a x =
                  match Type.finddesc a with
                    | Type.Var -> 
                        let refid, refcon = Type.Data.find_constructor "Ref" in
                          mkInW refid refcon x
                    | Type.NatW | Type.ZeroW | Type.OneW | Type.ContW _ -> 
                        mkTypeAnnot x (Some a)
                    | Type.TensorW(a1, a2) ->
                        let x1 = fresh_var () in
                        let x2 = fresh_var () in
                        mkLetW x ((x1, x2),
                                  mkPairW (pack a1 (mkVar x1)) (pack a2 (mkVar x2)))
                    | Type.DataW(id, ps) ->
                        if Type.Data.is_recursive id || Type.Data.is_mutable id then
                          x
                        else
                          begin
                            let cons = Type.Data.constructor_types id ps in
                            let y = fresh_var () in
                            mkCaseW id false x 
                              (Listutil.mapi (fun i t -> (y, mkInW id i (pack t (mkVar y)))) cons)
                          end
                    | Type.FunW _ | Type.FunU _ | Type.TensorU _ | Type.BoxU _ | Type.Link _ -> 
                        assert false in
                let rec unpack a x =
                  match Type.finddesc a with
                    | Type.Var -> 
                        let refid, refcon = Type.Data.find_constructor "Ref" in
                        let y = fresh_var () in
                          mkCaseW refid false x [(y, mkVar y)]
                    | Type.NatW | Type.ZeroW | Type.OneW | Type.ContW _ -> x
                    | Type.TensorW(a1, a2) ->
                        let x1 = fresh_var () in
                        let x2 = fresh_var () in
                        mkLetW x ((x1, x2),
                                  mkPairW (unpack a1 (mkVar x1)) (unpack a2 (mkVar x2)))
                    | Type.DataW(id, ps) ->
                        if Type.Data.is_recursive id || Type.Data.is_mutable id then
                          x
                        else
                          begin
                            let cons = Type.Data.constructor_types id ps in
                            let y = fresh_var () in
                            mkCaseW id false x 
                              (Listutil.mapi (fun i t -> (y, mkInW id i (unpack t (mkVar y)))) cons)
                          end
                    | Type.FunW _ | Type.FunU _ | Type.TensorU _ | Type.BoxU _ | Type.Link _ -> 
                        assert false in
                  (*
                  Printf.printf "\n\n%s\n\n" (Printing.string_of_termW 
                                          (unpack sigmaa (mkCallW fn (pack sigmaq (mkPairW sigma v)))));
                   *)
                let rlets, v' = reduce (unpack sigmaa (mkCallW fn (pack sigmaq (mkPairW sigma v)))) in
                let v1, v2 = fresh_var (), fresh_var () in
                  trace src w1.dst ((v', (v1, v2)) :: rlets @ lets) (mkVar v1, mkVar v2)
           | Force(w1, k) when w1.src = dst ->
               let newlets, sigma', k' = make_bindings sigma k in
                InDirect(src, "z", newlets @ lets, 
                         mkPairW k' (mkPairW (mkContW w1.dst (max_wire_src_dst + 1) sigma') v), possible_indirect_goals)
           | _ -> assert false
  in
  let sigma, x = "sigma", "x" in
  let entry_points = Hashtbl.create 10 in
  let rec trace_all src =
    if Hashtbl.mem entry_points src.name then []
    else 
      begin
        let block = trace src src.name [(mkVar "z",(sigma,x))] (mkVar sigma, mkVar x) in
  (*         Printf.printf "%s" (string_of_block block);  *)
          Hashtbl.add entry_points src.name ();
          match block with
            | Unreachable(_) | Return(_) -> [block]
            | Direct(_, _, _, _, dst) ->
                block :: trace_all dst
            | InDirect(_, _, _, _, dsts) ->
                block :: (List.concat (List.map trace_all dsts))
            | Branch(_, _, _, (_, _, cases)) ->
                block :: (List.concat (List.map (fun (_, _, dst) -> trace_all dst) cases))
      end in
  let blocks = trace_all {name = c.output.src; message_type = c.output.type_back} in
    { func_name = name;
      argument_type = c.output.type_back;
      entry_block = c.output.src;
      blocks = blocks;
      return_type = c.output.type_forward }

(* TODO: proper printing *)

let string_of_block b =
  let string_of_letbndgs bndgs =
    String.concat "" 
      (List.map (fun (t, (x, y)) -> 
                   Printf.sprintf "   let (%s, %s) = %s\n" 
                     x y (Printing.string_of_termW t)) (List.rev bndgs)) in
  match b with
    | Unreachable(l) -> 
        Printf.sprintf " l%i(x : %s) = unreachable" 
          l.name 
          (Printing.string_of_type l.message_type)
    | Direct(l, x, bndgs, body, goal) ->
        (Printf.sprintf " l%i(%s : %s) =\n" 
          l.name x (Printing.string_of_type l.message_type)) ^
        (string_of_letbndgs bndgs) ^
        (Printf.sprintf "   in l%i(%s) end\n" goal.name (Printing.string_of_termW body))
    | InDirect(l, x, bndgs, body, goals) ->
        (Printf.sprintf " l%i(%s : %s) =\n" 
          l.name x (Printing.string_of_type l.message_type)) ^
        (string_of_letbndgs bndgs) ^
        (Printf.sprintf "   in %s -> [%s] end\n" 
           (Printing.string_of_termW body)
           (String.concat "," (List.map (fun l -> Printf.sprintf "l%i" l.name) goals))
        )
    | Branch(la, x, bndgs, (id, cond, cases)) ->
        (Printf.sprintf " l%i(%s : %s) =\n" 
          la.name x (Printing.string_of_type la.message_type)) ^
        (string_of_letbndgs bndgs) ^
        (Printf.sprintf "    case %s of\n      | " (Printing.string_of_termW cond)) ^
        (String.concat "      | "
           (List.map (fun (cname, (l, lb, lg)) ->
                        Printf.sprintf "%s(%s) -> l%i(%s)\n" cname l lg.name (Printing.string_of_termW lb))
              (List.combine (Type.Data.constructor_names id) cases)
           ))
    | Return(l, x, bndgs, body, retty) ->
        (Printf.sprintf " l%i(%s) =\n  let" 
          l.name x (*(Printing.string_of_type l.message_type)*)) ^
        (string_of_letbndgs bndgs) ^
        (Printf.sprintf "   in %s\n end\n" 
           (Printing.string_of_termW body)
 (*           (Printing.string_of_type retty)*))

let string_of_func func =
  let buf = Buffer.create 80 in
    Buffer.add_string buf 
      (Printf.sprintf "%s(x : %s) : %s = l%i(x)\n\n"
         func.func_name
         (Printing.string_of_type func.argument_type)
         (Printing.string_of_type func.return_type)
         func.entry_block);
  List.iter (fun block -> 
               Buffer.add_string buf (string_of_block block);
               Buffer.add_string buf "\n"
  ) func.blocks;
  Buffer.contents buf
