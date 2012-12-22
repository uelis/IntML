(** Compilation of circuits to terms
*)
open Term
open Unify
open Typing
open Circuit

(* TODO: Hashtbl would be simpler *)  
module IntMap = Map.Make(
  struct
    type t = int
    let compare = compare
  end
)

(* Injection into the k-th component (from the left) of an n-fold sum. 
 * Assumes 0 <= k < n.
 *)
let rec in_k (k: int) (n: int) (t: Term.t): Term.t =
  assert (0 <= k && k < n);
  if k = 0 then
    mkInlW t
  else
    mkInrW (mkInW (Type.Data.sumid (n-1)) (k-1) t)

(* inverse to in_k: out_k (in_k k n t) n = (k, t) *)
let rec out_k (t: Term.t) (n: int) : int * Term.t =
  match t.desc with
  | InW(id, 0, s) when id = Type.Data.sumid 2 -> 
      (0, s)
  | InW(id, 1, {desc = InW(id', k, s)}) 
      when (id = Type.Data.sumid 2) && 
           (id' = Type.Data.sumid (n - 1)) -> 
      (k + 1, s)
  | _ -> failwith "out_k"


(** Compilation of string diagram into a lower-level term. *)
let message_passing_term (c: circuit): Term.t =
  (* Information about the wires in the graph *)
  let all_wires = wires c.instructions in
  let max_wire_src_dst = 
    List.fold_right (fun w m -> max w.src (max w.dst m)) all_wires 0 in
  (* Rename the variables in the instruction list so that
   * they do not clash with the name supply below.
   * *)
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
            node :: (i_fresh rest)
    in i_fresh c.instructions 
  in
  (* Supply of fresh variable names. 
   * (The instructions do not contain a free variable starting with "x")
   *)
  let fresh_var = Vargen.mkVarGenerator "x" ~avoid:[] in
  (* Build a map of nodes, indexed by the src-label of wires. 
   * Note: This uses the assumption that only one wire with a
   * given node-label appears in a graph *)
  let node_map_by_src = 
    let rec build_dst_map i =
      match i with
        | [] -> IntMap.empty
        | node :: rest -> 
            let ws = wires [node] in
            List.fold_right (fun w map -> IntMap.add w.src node map) ws
                            (build_dst_map rest) 
    in build_dst_map instructions_fresh in
  (* action finds the node to which dst is connected  
   * and returns the action that must happen if the token
   * is passed along that path
   *)
  let rec action dst = 
    let x = fresh_var() in
    let y = fresh_var() in
    let sigma, v, c, d = fresh_var(), fresh_var(), fresh_var(), fresh_var() in
    let to_dart d t = 
      (x, mkLetW (mkVar x) 
            ((sigma, v), in_k d (max_wire_src_dst + 1) t)) in
      try 
        begin
          match IntMap.find dst node_map_by_src with
            | Axiom(w1, f) when w1.src = dst -> 
                to_dart w1.src 
                  (mkPairW (mkVar sigma) 
                     (mkAppW (let_tupleW sigma f) (mkVar v)))
            | Tensor(w1, w2, w3) when w1.src = dst ->
                to_dart w3.src (mkPairW (mkVar sigma) (mkInlW (mkVar v)))
            | Tensor(w1, w2, w3) when w2.src = dst ->
                to_dart w3.src (mkPairW (mkVar sigma) (mkInrW (mkVar v)))
            | Tensor(w1, w2, w3) when w3.src = dst ->
                (x, mkLetW (mkVar x)
                           ((sigma, x),
                             mkCaseW (Type.Data.sumid 2) true (mkVar x) 
                                    [(v, in_k w1.src (max_wire_src_dst + 1) 
                                           (mkPairW (mkVar sigma) (mkVar v))) ;
                                     (v, in_k w2.src (max_wire_src_dst + 1) 
                                           (mkPairW (mkVar sigma) (mkVar v)))]
                             )
                )
            | Der(w1, w2, f) when w1.src = dst  ->
                (x, mkLetW (mkVar x) ((sigma, x),
                  mkLetW (mkVar x) ((c, v), 
                    in_k w2.src (max_wire_src_dst + 1) 
                      (mkPairW (mkVar sigma) (mkVar v))))
                )
            | Der(w1, w2, f) when w2.src = dst  ->
                (x, mkLetW (mkVar x) ((sigma, v),
                  in_k w1.src (max_wire_src_dst + 1) 
                    (mkPairW (mkVar sigma) 
                       (mkPairW (let_tupleW sigma f) (mkVar v)))
                ))
            | Case(id, w1, ws) when w1.src = dst  ->
                (x, mkLetW (mkVar x) ((sigma, v),
                  mkLetW (mkVar v) ((c, v),
                    mkCaseW id false (mkVar c) 
                      (List.map (fun w -> 
                                   (c, in_k w.src (max_wire_src_dst + 1) 
                                         (mkPairW (mkVar sigma) 
                                            (mkPairW (mkVar c) (mkVar v))))) ws)
                    )
                  )
                )
            | Case(id, w1, ws) when List.mem dst (List.map (fun w -> w.src) ws) -> 
                let n = List.length ws in
                let wsi = List.combine 
                            (List.map (fun w -> w.src) ws)
                            (Listutil.init n (fun i -> i)) in
                let i = List.assoc dst wsi in
                (x, mkLetW (mkVar x) ((sigma, v), 
                  mkLetW (mkVar v) ((c, y),
                    in_k w1.src (max_wire_src_dst + 1) 
                      (mkPairW (mkVar sigma) 
                         (mkPairW (mkInW id i (mkVar c)) (mkVar y)))
                  ) 
                ))
            | Grab(_, w1, wt) when w1.src = dst ->
                (x, mkLetW (mkVar x) ((sigma, unusable_var),
                                          in_k w1.src (max_wire_src_dst + 1) 
                                            (mkPairW (mkVar sigma)
                                               (mkLambdaW 
                                                  ((y, None), 
                                                   mkContW wt.src (max_wire_src_dst + 1)
                                                     (mkPairW (mkVar sigma) (mkVar y))
                                                  )
                                               )
                                            )))
            | Grab(_, w1, wt) when wt.src = dst ->
                ("x", mkLetW (mkVar "x") (("sigma", "v"), 
                                          mkLetW (mkVar "v") 
                                            (("k", "m"), 
                                             mkAppW (mkVar "k") (mkVar "m"))))
            | Force(w1, k) when w1.src = dst ->
                (x, mkLetW (mkVar x) ((sigma, y), 
                                          (mkAppW (let_tupleW sigma k) 
                                             (mkPairW 
                                                (mkLambdaW 
                                                   ((c, None), 
                                                    mkContW w1.src (max_wire_src_dst + 1) 
                                                      (mkPairW (mkVar sigma) (mkVar c))
                                                   )
                                                ) 
                                                (mkVar y)
                                             ))))
(*            | Memo(w1 (* X *) , w2 (* X *)) when w1.src = dst ->
                (x, mkLetW (mkVar x) (("sigma", "v"),
                                          in_k w2.src (max_wire_src_dst + 1) 
                                            (parse (Printf.sprintf
                                                      "case hashget (%i+1) 0 of \
                                                      inl(q) ->
                                                        let u = hashput (%i+1) q v in \
                                                         (sigma, v) \
                                                    | inr(q) -> (sigma, v)" w1.src w1.src))))
            | Memo(w1 (* X *) , w2 (* X *)) when w2.src = dst ->
                (x, mkLetW (mkVar x) (("sigma", "v"),
                             mkCaseW (parse (Printf.sprintf "hashget (%i+1) v" w1.src)) 
                                    [("a", in_k w2.src (max_wire_src_dst + 1) 
                                             (parse "(sigma,a)"));
                                     ("u", in_k w1.src (max_wire_src_dst + 1) 
                                           (parse (Printf.sprintf "let u = hashput (%i+1) 0 v in \
                                                   (sigma, v)" w1.src)))]
                             ))*)
            | Door(w1 (* X *) , w2 (* \Tens A X *)) when w1.src = dst ->
                (* <<sigma, c>, v> -> <sigma, <c, v>> *)
                (x, mkLetW (mkVar x) ((x, v),
                  mkLetW (mkVar x) ((sigma, c),
                    in_k w2.src (max_wire_src_dst + 1) 
                      (mkPairW (mkVar sigma) (mkPairW (mkVar c) (mkVar v))))
                ))
            | Door(w1 (* X *) , w2 (* \Tens A X *)) when w2.src = dst ->
                (* <sigma, <c, v>> -> <<sigma, c>, v> *)
                (x, mkLetW (mkVar x) ((sigma, x), 
                  mkLetW (mkVar x) ((c, v), 
                    in_k w1.src (max_wire_src_dst + 1) 
                      (mkPairW (mkPairW (mkVar sigma) (mkVar c)) (mkVar v)))))
            | ADoor(w1 (* \Tens (A x B) X *), 
                    w2 (* \Tens B X *)) when w1.src = dst ->
                (* <sigma, <<d, c>, v>> -> <<sigma, d>, <c, v>> *)
                (x, mkLetW (mkVar x) ((sigma, x), 
                  mkLetW (mkVar x) ((x, v), 
                    mkLetW (mkVar x) ((d, c), 
                      in_k w2.src (max_wire_src_dst + 1) 
                        (mkPairW (mkPairW (mkVar sigma) (mkVar d)) 
                           (mkPairW (mkVar c) (mkVar v)))))
                ))
            | ADoor(w1 (* \Tens (A x B) X *), 
                    w2 (* \Tens B X *)) when w2.src = dst ->
                (* <<sigma, d>, <c, v>> -> <sigma, <<d, c>, v>> *)
                (x, mkLetW (mkVar x) ((x, y),
                  mkLetW (mkVar x) ((sigma, d), 
                    mkLetW (mkVar y) ((c, v),
                      in_k w1.src (max_wire_src_dst + 1) 
                        (mkPairW (mkVar sigma) 
                           (mkPairW (mkPairW (mkVar d) (mkVar c)) (mkVar v)))))
                  ))
            | LWeak(w1 (* \Tens A X *), 
                    w2 (* \Tens B X *)) (* B <= A *) when w1.src = dst ->
                (* <sigma, <c, v>> @ w1 -> <sigma, <project b a c, v>> @ w2 *)
                let a = fst (Type.unTensorW (snd (Type.unTensorW w1.type_back))) in
                let b = fst (Type.unTensorW (snd (Type.unTensorW w2.type_forward))) in
                (x, mkLetW (mkVar x) 
                      ((sigma, y),
                       mkLetW (mkVar y) 
                         ((c, v), 
                          in_k w2.src (max_wire_src_dst + 1) 
                            (mkPairW (mkVar sigma) 
                               (mkPairW (mkAppW (project b a) (mkVar c)) 
                                  (mkVar v)))))
                  )
            | LWeak(w1 (* \Tens A X *), 
                    w2 (* \Tens B X *)) (* B <= A *) when w2.src = dst ->
                (* <sigma, <c, v>> @ w2 -> <sigma, <embed b a c, v>> @ w1 *)
                let a = fst (Type.unTensorW (snd (Type.unTensorW w1.type_forward))) in
                let b = fst (Type.unTensorW (snd (Type.unTensorW w2.type_back))) in
                (x, mkLetW (mkVar x) 
                      ((sigma, y),
                       mkLetW (mkVar y) 
                         ((c, v), 
                          in_k w1.src (max_wire_src_dst + 1) 
                            (mkPairW (mkVar sigma) 
                               (mkPairW (mkAppW (embed b a) (mkVar c)) 
                                  (mkVar v)))))
                  )
            | Epsilon(w1 (* [A] *), 
                      w2 (* \Tens A [B] *), 
                      w3 (* [B] *)) when w1.src = dst ->
                (* <sigma, v> @ w1 -> <sigma, <v,*>> @ w2 *)
                (x, mkLetW (mkVar x) ((sigma, v),
                  in_k w2.src (max_wire_src_dst + 1) 
                    (mkPairW (mkVar sigma) (mkPairW (mkVar v) mkUnitW)))
                )
            | Epsilon(w1 (* [A] *), 
                      w2 (* \Tens A [B] *), 
                      w3 (* [B] *)) when w2.src = dst ->
                (* <sigma, <c, v>> @ w2 -> <sigma, v> @ w3 *)
                (x, mkLetW (mkVar x) ((sigma, x), 
                  mkLetW (mkVar x) ((c, v), 
                    in_k w3.src (max_wire_src_dst + 1) 
                      (mkPairW (mkVar sigma) (mkVar v))
                  ))
                )
            | Epsilon(w1 (* [A] *), 
                      w2 (* \Tens A [B] *), 
                      w3 (* [B] *)) when w3.src = dst ->
                (* <sigma, v> @ w3 -> <sigma, *> @ w1 *)
                (x, mkLetW (mkVar x) ((sigma, v),
                  in_k w1.src (max_wire_src_dst + 1) 
                    (mkPairW (mkVar sigma) mkUnitW))
                ) 
            | _ -> 
                assert false
        end
      with 
        | Not_found ->
            if 0 = dst then (* output *)
              (x, in_k 0 (max_wire_src_dst + 1) (mkVar x))
            else (* wire must be unused because of weakening *)
              (x, mkConstW Cundef)
  in
  (* the term describing what happens to dart number k *)
  let rec part src wrs =
    match wrs with
      | [] -> 
            if 0 = src then
              action c.output.src  
            else 
              let x = fresh_var () in 
                (x, mkConstW Cundef)
      | w::rest ->
          if w.src = src then action w.dst else part src rest
  in
  let rec whole =
    let x = fresh_var () in
    let y = fresh_var () in
    let rec mkitoj i j = if i > j then [] else i :: (mkitoj (i+1) j) in
    (x, mkCaseW (Type.Data.sumid 2) true (mkVar x) 
          [part 0 all_wires;
            (y, mkCaseW (Type.Data.sumid (max_wire_src_dst + 1)) true (mkVar y) 
                  (List.map (fun k -> part k all_wires) 
                     (mkitoj 1 max_wire_src_dst)))])
  in 
  let (x, w) = whole in
    mkLambdaW ((x, None), w)

let termW_of_circuit (c: circuit) : Term.t * Type.t =
  (* Rename the wires so that the output wire has label 0 *)
  let pi i = 
    if i = 0 then c.output.dst else if i = c.output.dst then 0 else i in 
  let c' = { output = map_wire pi c.output;
             instructions = List.map (map_instruction pi) c.instructions} in
  let mp_term = message_passing_term c' in
  let compiled_term = mkTrW (mp_term) in 
    (* compiled_term has type 'a * X --> 'a * Y, we extract the X --> Y part.
     * Note: The compiled term is closed, so "x" cannot capture anything. *)
  let a = 
    let right_component ty = snd (Type.unTensorW ty) in
    Type.newty (Type.FunW(right_component (c.output.type_back), 
                          right_component (c.output.type_forward))) in  
    mkLambdaW (("x", None),
               mkLetW (mkAppW compiled_term (mkPairW mkUnitW (mkVar "x")))
                 ((unusable_var, "x"), mkVar "x")
    ),
    a
