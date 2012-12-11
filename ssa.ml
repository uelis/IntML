open Term
open Compile

type label = { 
  name: int; 
  message_type: Type.t
}
type let_bindings = (Term.t * (Term.var * Term.var)) list 
type block = 
    Unreachable of label
  | Direct of label * Term.var * let_bindings * Term.t * label
  | InDirect of label * Term.var * let_bindings * Term.t * (label list)
  | Branch of label * Term.var * let_bindings * (Term.t * (Term.var * Term.t * label) * (Term.var * Term.t * label))
  | Return of label * Term.var * let_bindings * Term.t * Type.t

let string_of_block b =
  match b with
    | Unreachable(l) -> 
        Printf.sprintf "and l%i(x) = L%i(x)\n" l.name l.name (* (Printing.string_of_type l.message_type)*)
    | Direct(l, x, bndgs, body, goal) ->
        (Printf.sprintf "and l%i(%s) = \n  let" 
          l.name x (* (Printing.string_of_type l.message_type)) *)) ^
        (String.concat "" (List.map (fun (t, (x, y)) -> 
                                       Printf.sprintf "  val (%s, %s) = %s\n" 
                                         x y (Printing.string_of_termW t)) (List.rev bndgs))) ^
        (Printf.sprintf "  in l%i(%s) end\n" goal.name (Printing.string_of_termW body))
    | Branch(la, x, bndgs, (cond, (l, lb, lg), (r, rb, rg))) ->
        (Printf.sprintf "and l%i(%s)=\n  let" 
          la.name x (* (Printing.string_of_type la.message_type)*)) ^
        (String.concat "" (List.map (fun (t, (x, y)) -> 
                                       Printf.sprintf "  val (%s, %s) = %s\n" 
                                         x y (Printing.string_of_termW t)) (List.rev bndgs))) ^
        (Printf.sprintf "  in case %s of\n" (Printing.string_of_termW cond)) ^
        (Printf.sprintf "    inl(%s) => l%i(%s)\n" l lg.name (Printing.string_of_termW lb)) ^
        (Printf.sprintf "  | inr(%s) => l%i(%s)\nend\n" r rg.name (Printing.string_of_termW rb)) 
    | Return(l, x, bndgs, body, retty) ->
        (Printf.sprintf "and l%i(%s)=\n  let" 
          l.name x (*(Printing.string_of_type l.message_type)*)) ^
        (String.concat "" (List.map (fun (t, (x, y)) -> 
                                       Printf.sprintf "  val (%s, %s) = %s\n" 
                                         x y (Printing.string_of_termW t)) (List.rev bndgs))) ^
        (Printf.sprintf "  in %s\n end\n" 
           (Printing.string_of_termW body)
 (*           (Printing.string_of_type retty)*))


type func = {
  func_name : string;
  argument_type: Type.t;
  entry_block : int;
  blocks : block list;
  return_type: Type.t;
}

let fresh_var = Vargen.mkVarGenerator "x" ~avoid:[]

let rec isPure (t: Term.t) : bool =
  match t.Term.desc with
    | Var(_) -> true
    | UnitW -> true
    | ConstW(Cbot) -> true (* TODO: Cbot is actually "assert false" *)
    | ConstW(Cprint(_)) | ConstW(Cintprint)-> false
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
    | Var(_) | ConstW(_) | UnitW | LoopW(_) | FoldW(_) |  LambdaW(_) | AssignW _ | DeleteW _ -> t
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
              | CaseW(s1, [(x, sx); (y, sy)]) ->
                  let x' = fresh_var () in
                  let y' = fresh_var () in
                  let sx' = Term.rename_vars (fun z -> if z = x then x' else if z = y then y' else z) sx in
                  let sy' = Term.rename_vars (fun z -> if z = x then x' else if z = y then y' else z) sy in
                    mkCaseW s1 [(x', reduce (mkCaseW sx' [(u, su); (v, sv)])); 
                                (y', reduce (mkCaseW sy' [(u, su); (v, sv)]))]
              | _ -> 
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

let trace (c: circuit) : func =
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
    let rec make_bindings t (vars, f) =
      match vars with 
        | [] -> [], t, f
        | x :: rest ->
            let th = fresh_var () in
            let tr = fresh_var () in
            let f' = Term.rename_vars (fun u -> if u = x then tr else u) f in
            let lets, t', f'' = make_bindings (mkVar th) (rest, f') in
              lets @ [(t, (th, tr))], mkPairW t' (mkVar tr), f'' in
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
                trace src w1.dst (newlets @ lets) (sigma', reduce (mkAppW f' v))
          (*            Direct(src, newlets @ lets, 
           (sigma', mkAppW f' v), 
           {name = w1.dst; message_type = w1.type_forward})*)
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
                      (* Printf.printf "%s\n" (Printing.string_of_termW v); *)
                      let v' = "v'" in 
                        (*                      assert (Type.equals src.message_type w3.type_back);*)
                        Branch(src, "z", lets,
                               (v, 
                                (v', mkPairW sigma (mkVar v'), {name = w1.dst; message_type = w1.type_forward}), 
                                (v', mkPairW sigma (mkVar v'), {name = w2.dst; message_type = w2.type_forward})))
              end
          | Der(w1 (* \Tens A X *), w2 (* X *), f) when dst = w1.src ->
              trace src w2.dst lets (sigma, reduce (mkSndW v))
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
              trace src w3.dst lets (sigma, reduce (mkSndW v))
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
                        let c = fresh_var () in
                          (*                      assert (Type.equals src.message_type w1.type_back); *)
                          Branch(src, "z", lets', 
                                 (c', 
                                  (c, mkPairW sigma (mkPairW (mkVar c) v'), {name = w2.dst; message_type = w2.type_forward}),
                                  (c, mkPairW sigma (mkPairW (mkVar c) v'), {name = w3.dst; message_type = w3.type_forward})))
              end
(*            | Grab(w1, wt) when w1.src = dst ->
                trace src w1.dst lets (sigma, mk
                ("x", mkLetW (mkVar "x") (("sigma", "v"),
                                          in_k w1.src (max_wire_src_dst + 1) 
                                            (mkPairW (mkVar "sigma")
                                               (mkLambdaW 
                                                  (("m", None), 
                                                   in_k wt.src (max_wire_src_dst + 1) 
                                                     (mkPairW (mkVar "sigma") (mkVar "m"))
                                                  )
                                               )
                                            )))
            | Grab(w1, wt) when wt.src = dst ->
                ("x", mkLetW (mkVar "x") (("sigma", "v"), 
                                            (parse ("let (contk, m) = v in contk m"))))
            | Force(w1, k) when w1.src = dst ->
                (x, mkLetW (mkVar x) ((sigma, y), 
                                          (mkAppW (let_tupleW sigma k) 
                                             (mkPairW 
                                                (mkLambdaW 
                                                   (("m", None), 
                                                    in_k w1.src (max_wire_src_dst + 1) 
                                                      (mkPairW (mkVar sigma) (mkVar "m"))
                                                   )
                                                ) 
                                                (mkVar y)
                                             )))) *)
          | _ -> assert false
  in
  let sigma, x = "sigma", "x" in
  let entry_points = Hashtbl.create 10 in
  let rec trace_all src =
    if Hashtbl.mem entry_points src.name then []
    else 
      begin
        let block = trace src src.name [(mkVar "z",(sigma,x))] (mkVar sigma, mkVar x) in
          Printf.printf "%s" (string_of_block block);
          Hashtbl.add entry_points src.name ();
          match block with
            | Unreachable(_) | Return(_) -> [block]
            | Direct(_, _, _, _, dst) ->
                block :: trace_all dst
            | Branch(_, _, _, (_, (_, _, dst1), (_, _, dst2))) ->
                block :: trace_all dst1 @ trace_all dst2 
      end in
  let blocks = trace_all {name = c.output.src; message_type = c.output.type_back} in
    { func_name = "f";
      argument_type = c.output.type_back;
      entry_block = c.output.src;
      blocks = blocks;
      return_type = c.output.type_forward }
