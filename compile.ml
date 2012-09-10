(** Compilation to circuits
*)
open Term
open Unify
open Typing

(* Conveniencene function for n-ary let on WC level *)          
let let_tupleW (x: var) ((sigma: var list), (f: Term.t)) : Term.t =
  (* TODO: document *)
  let rec remove_shadow sigma =
    match sigma with
      | [] -> []
      | x :: rest -> 
          x :: remove_shadow 
                 (List.map (fun y -> if x = y then Term.unusable_var else y) 
                    rest)
  in 
  let rec let_tuple x (sigma, f) =
    match sigma with 
      | [] -> f
      | z :: rest ->
          mkLetW  (mkVar x) ((x, z), let_tuple x (rest, f)) 
  in let_tuple x (remove_shadow sigma, f)       

let unTensorW a =
  match Type.finddesc a with
    | Type.TensorW(a1, a2) -> a1, a2
    | _ -> assert false

(** A wire represents a dart in an undirected graph. *)
type wire = {
  src: int;
  dst: int;
  type_forward: Type.t;
  type_back: Type.t
}

let flip (w: wire) = {
  src = w.dst;
  dst = w.src;
  type_forward = w.type_back;
  type_back = w.type_forward
}                       
(* TODO: DOCUMENTATION
 * Graph invariant: There are no two wires with w1.src = w2.src that are affixed
 * to different nodes. I.e. w.src and w.dst are darts and must therefore be
 * unique in the graph *)

(* All wires are meant to 'leave' the instructions, i.e. they are all affixed
*  with their src-label to the instruction.
*  The type of the respective wires is indicated in the comments. *)
type instruction =
     Axiom of wire (* [f] *) * (Term.var list * Term.t)
   | Tensor of wire (* X *) * wire (* Y *) * wire (* X \otimes Y *)
   | Der of wire (* \Tens A X *) * wire (* X *) * (Term.var list * Term.t)
   | Contr of wire (* \Tens{A+B} X *) * wire (* \Tens A X *) * wire (* \Tens B X *)
   | Door of wire (* X *) * wire (* \Tens A X *)
   | ADoor of wire (* \Tens (A x B) X *) * wire (* \Tens B X *) 
   | LWeak of wire (* \Tens A X *) * wire (* \Tens B X *) (* where B <= A *)
   | Epsilon of wire (* [A] *) * wire (* \Tens A [B] *) * wire (* [B] *)

type circuit = 
    { output : wire; 
      instructions : instruction list
    }

let rec wires (i: instruction list): wire list =
  match i with
    | [] -> []
    | Axiom(w1, _) :: is -> w1 :: (wires is)
    | Tensor(w1, w2, w3) :: is -> w1 :: w2 :: w3 :: (wires is)
    | Der(w1, w2, _) :: is -> w1 :: w2 :: (wires is)
    | Contr(w1, w2, w3) :: is -> w1 :: w2 :: w3 :: (wires is)
    | Door(w1, w2) :: is -> w1 :: w2 :: (wires is)
    | ADoor(w1, w2) :: is -> w1 :: w2 :: (wires is)
    | LWeak(w1, w2) :: is -> w1 :: w2 :: (wires is)
    | Epsilon(w1, w2, w3) :: is -> w1 :: w2 :: w3 :: (wires is)

let map_wires_instruction (f: wire -> wire): instruction -> instruction =
  fun i -> 
    match i with
    | Axiom(w, t) -> Axiom(f w, t)
    | Tensor(w1, w2, w3) -> Tensor(f w1, f w2, f w3)
    | Der(w1, w2, t) -> Der(f w1, f w2, t)
    | Contr(w1, w2, w3) -> Contr(f w1, f w2, f w3)
    | Door(w1, w2) -> Door(f w1, f w2)
    | ADoor(w1, w2) -> ADoor(f w1, f w2)
    | LWeak(w1, w2) -> LWeak(f w1, f w2)
    | Epsilon(w1, w2, w3) -> Epsilon(f w1, f w2, f w3)

(* renaming of wires *)                               
let map_wire (f: int -> int): wire -> wire =
  fun w -> 
    {src = f w.src;
     dst = f w.dst;
     type_forward = w.type_forward;
     type_back = w.type_back
    }

let map_instruction (f: int -> int): instruction -> instruction =
  map_wires_instruction (map_wire f) 

(* Wires for all the variables in the context. 
 * They point into the graph with their dst-label. *)
type ctx = (var * wire) list

module U = Unify(struct type t = unit end)

(**
  * Compilation of an upper-level term to a string diagram.
  *
  * The diagram is assumed to reside in a box of the functor
  * {\Tens {An * ... * A1}}. The components of the tuples
  * are named by the variable names in sigma.
  *
  * Arguments:
  * - sigma: Names with which the components can be accessed.
  *     sigma = [c1; ... ;cn] means that c1 corresponds to
  *     A1 and cn to An
  * - gamma: Names of the wires for the context variables. 
  *     They are directed so as to go into the diagram.
  * - t: the term that is to be compiled.
  *
  * Result:
  * - The wire that comes out of the diagram with the value of
  *   the term t.
  * - The diagram as a list of instructions.
  *)
(* ASSUMPTION: all type annotations in t may only contain index types
 * that are variables, i.e. not {1+1}'a --o 'b, for example. *)
let circuit_of_termU  (sigma: var list) (gamma: ctx) (t: Term.t): circuit = 
  let used_wirenames = 
    List.fold_right (fun (_, w) wns -> w.src :: w.dst :: wns) gamma [] in 
  let next_wirename = ref ((List.fold_right max used_wirenames (-1)) + 1) in
  let fresh_wire () = 
    let n = !next_wirename in
      next_wirename := !next_wirename + 2;
      { src = n;
        dst = n + 1;
        type_forward = Type.newty Type.Var;
        type_back = Type.newty Type.Var
      } in
  let rec enter_box (gamma: ctx) : ctx * instruction list =
    match gamma with 
      | [] -> ([], [])
      | (x, w) :: rest ->
          let (d, i) = enter_box rest in 
          let w' = fresh_wire () in 
          let w'' = fresh_wire () in 
            ((x, w') :: d, LWeak(flip w, w'')::ADoor(flip w'', w') :: i) 
  in
  let rec compile (sigma: var list) (gamma: ctx) (t: Term.t) =
    match t.desc with
      | Var(x) -> 
          let wx = List.assoc x gamma in 
          let w = fresh_wire () in 
          let w' = fresh_wire () in 
            (w, [Der(flip w', w, 
                     (sigma, mkUnitW));
                 LWeak(flip wx, w')])
      | HackU(_, t1) ->
          let w = fresh_wire () in
            (w, [(Axiom(w, (sigma, fresh_vars_for_missing_annots t1)))])
      | PairU(s, t) ->
          let fv_s = free_vars s in
          let fv_t = free_vars t in
          let gamma_s = List.filter (fun (x,a) -> List.mem x fv_s) gamma in
          let gamma_t = List.filter (fun (x,a) -> List.mem x fv_t 
                                     && (not (List.mem x fv_s))) gamma in
          let (w_s, i_s) = compile sigma gamma_s s in
          let (w_t, i_t) = compile sigma gamma_t t in
          let w = fresh_wire () in
            (w, Tensor(flip w_s, flip w_t, w) :: i_s @ i_t)
      | LetU(s, (x, y, t)) ->
          let fv_s = free_vars s in
          let fv_t = free_vars t in
          let gamma_s = List.filter (fun (x,a) -> List.mem x fv_s) gamma in
          let (gamma_s_inbox, i_enter_box) = enter_box gamma_s in
          let (w_s, i_s) = compile sigma gamma_s_inbox s in
          let w_s_left = fresh_wire () in 
          let w_s_right = fresh_wire () in 
          let i_unpair = [Tensor(w_s_left, w_s_right, flip w_s)] in
          let w_x = fresh_wire () in 
          let w_y = fresh_wire () in 
          let i_leavebox = [Door(flip w_s_left, w_x); 
                            Door(flip w_s_right, w_y)] in
          let gamma_t = List.filter (fun (x,a) -> List.mem x fv_t 
                                     && (not (List.mem x fv_s))) gamma in
          let (w_t, i_t) = compile sigma ((y, w_y) :: (x, w_x) :: gamma_t) t in
            (w_t, i_t @ i_s @ i_enter_box @ i_unpair @ i_leavebox)
      | AppU(s, t) ->
          let fv_s = free_vars s in
          let fv_t = free_vars t in
          let gamma_s = List.filter (fun (x,a) -> List.mem x fv_s) gamma in
          let gamma_t = List.filter (fun (x,a) -> List.mem x fv_t 
                                     && (not (List.mem x fv_s))) gamma in
          let (w_s, i_s) = compile sigma gamma_s s in
          let (w_t, i_t) = compile_in_box unusable_var sigma gamma_t t in
          let wr = fresh_wire () in 
            (wr, Tensor(flip w_t, wr, flip w_s) :: i_s @ i_t)
      | CopyU(s, (x,y, t)) ->
          let fv_s = free_vars s in
          let fv_t = free_vars t in
          let gamma_s = List.filter (fun (x,a) -> List.mem x fv_s) gamma in
          let gamma_t = List.filter (fun (x,a) -> List.mem x fv_t 
                                     && (not (List.mem x fv_s))) gamma in
          let (w_s, i_s) = compile_in_box unusable_var sigma gamma_s s in
          let w_x = fresh_wire () in
          let w_y = fresh_wire () in
          let (w_t, i_t) = compile sigma ((x, w_x) :: (y, w_y) :: gamma_t) t in
            (w_t, Contr(flip w_s, w_x, w_y) :: i_s @ i_t)
      | CaseU(f, (x, s), (y, t)) ->
          let duplicate_and_enter_wire (w: wire) 
                : wire * wire * instruction list =
            let w', wl, wr = fresh_wire (), fresh_wire (), fresh_wire () in
            let wl_in_box, wr_in_box = fresh_wire (), fresh_wire () in
            (wl_in_box, wr_in_box, 
             [Der(w', flip w, (sigma, fresh_vars_for_missing_annots f)); 
              Contr(flip w', wl, wr);
              Door(wl_in_box, flip wl); Door(wr_in_box, flip wr)])
          in 
          let rec duplicate_and_enter_ctx (c: ctx)
                : ctx * ctx * instruction list =
            match c with 
              | [] -> ([], [], [])
              | (x, w) :: rest -> 
                  let (wl, wr, is) = duplicate_and_enter_wire w in
                  let (dl, dr, i') = duplicate_and_enter_ctx rest in
                    ((x, wl) :: dl, (x, wr) :: dr, is @ i')
          in
          let (gammal, gammar, i_dup) = duplicate_and_enter_ctx gamma in
          let (w_s_in_box, i_s) = compile (x :: sigma) gammal s in
          let (w_t_in_box, i_t) = compile (y :: sigma) gammar t in
          let w_s, w_t = fresh_wire (), fresh_wire () in
          let i_leavebox = [Door(flip w_s_in_box, w_s); 
                            Door(flip w_t_in_box, w_t)] in
          let w_join = fresh_wire () in
          let i_join = [Contr(w_join, flip w_s, flip w_t)] in
          let w = fresh_wire () in
          let i_der = [Der(flip w_join, w, 
                           (sigma, fresh_vars_for_missing_annots f))] in
            (w, i_der @ i_join @ i_leavebox @ i_s @ i_t @ i_dup)
      | BoxTermU(t) ->
          let w = fresh_wire () in
            (w, [Axiom(w, 
                       (sigma, mkLambdaW ((unusable_var, Some (Type.newty Type.OneW)), 
                                          fresh_vars_for_missing_annots t)))])
      | LetBoxU(s, (c, t)) ->
          let fv_s = free_vars s in
          let fv_t = free_vars t in
          let gamma_s = List.filter (fun (x,a) -> List.mem x fv_s) gamma in
          let gamma_t = List.filter (fun (x,a) -> List.mem x fv_t 
                                     && (not (List.mem x fv_s))) gamma in
          let wr = fresh_wire () in 
          let (w_s, i_s) = compile sigma gamma_s s in
          let (w_t, i_t) = compile_in_box c sigma gamma_t t in
            (wr, Epsilon(flip w_s, flip w_t, wr) :: i_s @ i_t)
      | LambdaU((x, None), s) ->
          let wx = fresh_wire () in
          let w = fresh_wire () in
          let (w_s, i_s) = (compile sigma ((x, wx) :: gamma) s) in
            (w, Tensor(wx, flip w_s, w) :: i_s)
      | LambdaU((x, Some ty), s) ->
          let tym, typ = Type.question_answer_pair (Type.freshen_index_types ty) in
          let alpha1, alpha2 = Type.newty Type.Var, Type.newty Type.Var in
          let sigma1, sigma2 = Type.newty Type.Var, Type.newty Type.Var in
          let tyTensor (s, t) = Type.newty (Type.TensorW(s, t)) in
            (* ASSUMPTION: all annotations must have type variables as index
            * types.
            * TODO: Give a warning otherwise! *)
          let wx = 
            { (fresh_wire ()) with 
                  type_forward = tyTensor(sigma1, tyTensor(alpha1, typ));
                  type_back = tyTensor(sigma2, tyTensor(alpha2, tym))} in 
          let w = fresh_wire () in
          let (w_s, i_s) = (compile sigma ((x, wx) :: gamma) s) in
            (w, Tensor(wx, flip w_s, w) :: i_s)
      | TypeAnnot (t, None) -> 
          compile sigma gamma t
      | TypeAnnot (t, Some ty) -> 
          let (w, ins) = compile sigma gamma t in
          let tyTensor (s, t) = Type.newty (Type.TensorW(s, t)) in
          let sigma1, sigma2 = Type.newty Type.Var, Type.newty Type.Var in
          let tym, typ = Type.question_answer_pair (Type.freshen_index_types ty) in
            U.unify w.type_forward (tyTensor(sigma1, typ));
            U.unify w.type_back (tyTensor(sigma1, tym)); 
            (w, ins)
      | TrW _|LambdaW (_, _)|AppW (_, _)|CaseW (_, _)| InW (_, _, _)
      | LetBoxW(_,_) | LetW (_, _)|PairW (_, _)|ConstW (_)|UnitW
      | FoldW _ | UnfoldW _ ->
          assert false 
  and compile_in_box (c: var) (sigma: var list) (gamma: ctx) (t: Term.t) =
    let (gamma_in_box, i_enter_box) = enter_box gamma in
    let (w_t, i_t) = compile (c :: sigma) gamma_in_box t in
    let w = fresh_wire () in 
      (w, Door(flip w_t, w) :: i_t @ i_enter_box)
  in 
  let w, is = compile sigma gamma t in
    { output = w; instructions = is }


(*
 * Infers types in the string diagram and instantiated the
 * terms in the Der- and Axiom-nodes so that the pre_term 
 * computed below will in fact be a proper term and we 
 * won't have to run type inference on it.
 *
 * Inequality constraints are solved *after* all other equality constraints are
 * solved. This corresponds to first computing the constraints that the rules
 * impose locally and then connecting them with the inequality constraints.
 * TODO: We should prove that this is correct!
 *)
let infer_types (c : circuit) : Type.t =
  let tensor s t = Type.newty (Type.TensorW(s, t)) in
  let sum s t = Type.newty (Type.SumW [s; t]) in
  let rec constraints (instructions: instruction list) 
        : Typing.type_constraint list  =
    match instructions with
      | [] -> []
      | Axiom(w1, (s, f))::rest -> 
          let sigma = Type.newty Type.Var in
          let alpha = Type.newty Type.Var in
          let x, y = "x", "y" in
          let f' = variant f in (* ensure "x" and "y" are fresh *) 
          let s' = List.map variant_var s in
          let tyfapp = principal_typeW
                                [(x, sigma); (y, alpha)] 
                                (mkAppW (let_tupleW x (s', f')) (mkVar y)) in 
            Typing.eq_constraint 
              w1.type_forward 
              (Type.newty (Type.TensorW(sigma, tyfapp))) ::
            Typing.eq_constraint 
              (flip w1).type_forward 
              (Type.newty (Type.TensorW(sigma, alpha))) ::
            (constraints rest) 
      | Tensor(w1, w2, w3)::rest ->
          let sigma1 = Type.newty Type.Var in
          let alpha1 = Type.newty Type.Var in
          let beta1 = Type.newty Type.Var in
            Typing.eq_constraint 
              w3.type_forward (tensor sigma1 (sum alpha1 beta1)) ::
            Typing.eq_constraint 
              w1.type_back (tensor sigma1 alpha1) ::
            Typing.eq_constraint 
              w2.type_back (tensor sigma1 beta1) ::
            let sigma2 = Type.newty Type.Var in
            let alpha2 = Type.newty Type.Var in
            let beta2 = Type.newty Type.Var in
            Typing.eq_constraint 
              w1.type_forward (tensor sigma2 alpha2) ::
            Typing.eq_constraint 
              w2.type_forward (tensor sigma2 beta2) ::
            Typing.eq_constraint 
              w3.type_back
              (tensor sigma2 (sum alpha2 beta2)) ::
            (constraints rest)
      | Der(w1, w2, (s, f))::rest ->
          let sigma1 = Type.newty Type.Var in
          let alpha1 = Type.newty Type.Var in
          let beta1 = Type.newty Type.Var in
            Typing.eq_constraint
              w2.type_forward (tensor sigma1 beta1) ::
            Typing.eq_constraint
              w1.type_back (tensor sigma1 (tensor alpha1 beta1)) ::
            let sigma2 = Type.newty Type.Var in
            let alpha2 = Type.newty Type.Var in
            let x = "x" in
            (* ensure "x" is fresh *)
            let f' = variant f in
            let s' = List.map variant_var s in
            let tyf = principal_typeW [(x, sigma2)] (let_tupleW x (s', f')) in 
            Typing.eq_constraint
              w1.type_forward (tensor sigma2 (tensor tyf alpha2)) ::
            Typing.eq_constraint
              w2.type_back (tensor sigma2 alpha2) ::
            (constraints rest)
      | Contr(w1 (* \Tens{A+B} X *), 
              w2 (* \Tens A X *), w3 (* \Tens B X *)) :: rest ->
          let sigma1 = Type.newty Type.Var in
          let alpha1 = Type.newty Type.Var in
          let beta1 = Type.newty Type.Var in
          let gamma1 = Type.newty Type.Var in
            Typing.eq_constraint
              w1.type_forward 
              (tensor sigma1 (tensor (sum alpha1 beta1) gamma1)) ::
            Typing.eq_constraint
              w2.type_back (tensor sigma1 (tensor alpha1 gamma1)) ::
            Typing.eq_constraint
              w3.type_back (tensor sigma1 (tensor beta1 gamma1)) ::
            let sigma2 = Type.newty Type.Var in
            let alpha2 = Type.newty Type.Var in
            let beta2 = Type.newty Type.Var in
            let gamma2 = Type.newty Type.Var in
            Typing.eq_constraint
              w2.type_forward 
              (tensor sigma2 (tensor alpha2 gamma2)) ::
            Typing.eq_constraint
              w3.type_forward
              (tensor sigma2 (tensor beta2 gamma2)) ::
            Typing.eq_constraint
              w1.type_back 
              (tensor sigma2 (tensor (sum alpha2 beta2) gamma2)) ::
            (constraints rest)
      | Door(w1 (* X *) , w2 (* \Tens A X *))::rest ->
          let sigma1 = Type.newty Type.Var in
          let alpha1 = Type.newty Type.Var in
          let beta1 = Type.newty Type.Var in
            Typing.eq_constraint
              w2.type_forward (tensor sigma1 (tensor alpha1 beta1)) ::
            Typing.eq_constraint
              w1.type_back
              (tensor (tensor sigma1 alpha1) beta1) ::
            let sigma2 = Type.newty Type.Var in
            let alpha2 = Type.newty Type.Var in
            let beta2 = Type.newty Type.Var in
            Typing.eq_constraint
              w1.type_forward
              (tensor (tensor sigma2 alpha2) beta2) ::
            Typing.eq_constraint
              w2.type_back
              (tensor sigma2 (tensor alpha2 beta2)) ::
            (constraints rest)
      | ADoor(w1 (* \Tens (A x B) X *), w2 (* \Tens B X *))::rest ->
          let sigma1 = Type.newty Type.Var in
          let alpha1 = Type.newty Type.Var in
          let beta1 = Type.newty Type.Var in
          let gamma1 = Type.newty Type.Var in
            Typing.eq_constraint
              w2.type_forward 
              (tensor (tensor sigma1 alpha1) (tensor beta1 gamma1)) ::
            Typing.eq_constraint
              w1.type_back 
              (tensor sigma1 (tensor (tensor alpha1 beta1) gamma1)) ::
            let sigma2 = Type.newty Type.Var in
            let alpha2 = Type.newty Type.Var in
            let beta2 = Type.newty Type.Var in
            let gamma2 = Type.newty Type.Var in
            Typing.eq_constraint
              w1.type_forward 
               (tensor sigma2 (tensor (tensor alpha2 beta2) gamma2)) ::
            Typing.eq_constraint
              w2.type_back
              (tensor (tensor sigma2 alpha2) (tensor beta2 gamma2)) ::
            (constraints rest)
      | LWeak(w1 (* \Tens A X*), w2 (* \Tens B X*)) (* B <= A *)::rest ->
          let sigma = Type.newty Type.Var in
          let alpha = Type.newty Type.Var in
          let beta = Type.newty Type.Var in
          let gamma1 = Type.newty Type.Var in
          let gamma2 = Type.newty Type.Var in
            Typing.eq_constraint
              w1.type_forward (tensor sigma (tensor alpha gamma1)) :: 
            Typing.eq_constraint
              w1.type_back (tensor sigma (tensor alpha gamma2)) :: 
            Typing.eq_constraint
              w2.type_forward (tensor sigma (tensor beta gamma2)) :: 
            Typing.eq_constraint
              w2.type_back (tensor sigma (tensor beta gamma1)) :: 
            Typing.leq_constraint beta alpha :: 
            (constraints rest)
      | Epsilon(w1 (* [A] *), w2 (* \Tens A [B] *), w3 (* [B] *)) :: rest ->
          let sigma1 = Type.newty Type.Var in
          let alpha1 = Type.newty Type.Var in
            Typing.eq_constraint
             w2.type_forward 
           (tensor sigma1 (tensor alpha1 (Type.newty Type.OneW))) ::
            Typing.eq_constraint
             w1.type_back 
           (tensor sigma1 alpha1) ::
          let sigma2 = Type.newty Type.Var in
          let beta2 = Type.newty Type.Var in
            Typing.eq_constraint
              w3.type_forward (tensor sigma2 beta2) ::
            Typing.eq_constraint
              w2.type_back 
              (tensor sigma2 (tensor alpha1 beta2))::
            let sigma3 = Type.newty Type.Var in
            Typing.eq_constraint
              w1.type_forward (tensor sigma3 (Type.newty Type.OneW)) ::
            Typing.eq_constraint
              w3.type_back (tensor sigma3 (Type.newty Type.OneW)) ::
            (constraints rest) in
    try
      Typing.solve_constraints (constraints c.instructions);
      let right_component ty =
        match Type.finddesc ty with 
          | Type.TensorW(_, r) -> r
          | _ -> failwith "Internal error: output wire has wrong type" in
        Type.newty (Type.FunW(right_component (c.output.type_back), 
                              right_component (c.output.type_forward))) 
    with 
      | U.Not_Unifiable _ -> 
          failwith "Internal error: cannot unify constraints in compilation"

module IntMap = Map.Make(
  struct
    type t = int
    let compare = compare
  end
)

let rec dot_of_circuit 
      ?title:(title = "")
      ?wire_style:(wire_style = fun w -> "") 
      (c: circuit) : string = 
  let node_name ins =
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
  in 
  let node_label ins =
    let ws = wires [ins] in
    let name =
        match ins with
          | Axiom(_, (_, { desc= LambdaW((x, None), _) })) 
              when x = unusable_var -> "[...]"
          | Axiom(_, _) -> "hack(...)"
          | Tensor(_, _, _) -> "&otimes;"
          | Der(_, _, _) -> "&pi;_..."
          | Contr(_, _, _) -> "a+"
          | Door(_, w) -> 
              if w.src = -1 then "\", shape=\"plaintext" else "&uarr;"
          | ADoor(_, _) -> "&darr;"
          | LWeak(_, _) -> "lweak"
          | Epsilon(_, _, _) -> "&pi;"
    in 
      List.fold_right (fun w s -> Printf.sprintf "%s(%i)" s w.src) ws name 
  in 
  let instructions_with_result = 
    (Door(flip c.output, 
          { src = (-1);
            dst = (-2); 
            type_forward = Type.newty Type.Var; 
            type_back = Type.newty Type.Var})) :: c.instructions in
  let node_map_by_src = 
    let rec build_dst_map i =
      match i with
        | [] -> IntMap.empty
        | node :: rest -> 
            List.fold_right (fun w map -> IntMap.add w.src node map) 
              (wires [node]) (build_dst_map rest) 
    in build_dst_map instructions_with_result in
  let buf = Buffer.create 1024 in
  let nodes () = 
    List.iter (fun ins -> 
                 Buffer.add_string buf (node_name ins);
                 Buffer.add_string buf "[label=\"";
                 Buffer.add_string buf (node_label ins);
                 Buffer.add_string buf "\"];\n") instructions_with_result 
  in
  let edges () =
    let edge srcins (w: wire) =
      try
        let dstins = IntMap.find w.dst node_map_by_src in
          Buffer.add_string buf (node_name srcins);
          Buffer.add_string buf " -> ";
          Buffer.add_string buf (node_name dstins);
          Buffer.add_string buf (wire_style w);
          Buffer.add_string buf ";\n ";
      with Not_found -> () (* Weakening *) in
      List.iter (fun srcins -> List.iter (edge srcins) (wires [srcins])) 
        instructions_with_result 
  in
    Buffer.add_string buf "digraph G {\n labelloc=t; label=\"";
    Buffer.add_string buf title;
    Buffer.add_string buf "\";fontname=Monospace;fontcolor=blue;fontsize=36;";
    nodes ();
    edges ();
    Buffer.add_string buf "}";
    Buffer.contents buf

(* Injection into the k-th component (from the left) of an n-fold sum. 
 * Assumes 0 <= k < n.
 *)
let rec in_k (k: int) (n: int) (t: Term.t): Term.t =
  assert (0 <= k && k < n);
  if k = 0 then
    mkInlW t
  else
    mkInrW (mkInW (n-1) (k-1) t)

(* inverse to in_k: out_k (in_k k n t) n = (k, t) *)
let rec out_k (t: Term.t) (n: int) : int * Term.t =
  match t.desc with
  | InW(2, 0, s) -> (0, s)
  | InW(2, 1, {desc = InW(n', k, s)}) when n = n' + 1 -> (k + 1, s)
  | _ -> failwith "out_k"

exception Not_Leq               

let rec min (ty: Type.t) : Term.t =
  match Type.finddesc ty with
  | Type.Var -> mkUnitW
  | Type.OneW -> mkUnitW
  | Type.NatW -> mkConstW (Cintconst(0))
  | Type.TensorW(a, b) -> mkPairW (min a) (min b)
  | Type.SumW(a :: l) -> mkInW (1 + (List.length l)) 0 (min a)
  | Type.MuW(alpha,a) -> 
      let mua = Type.newty (Type.MuW(alpha, a)) in
      let unfolded = Type.subst (fun beta -> 
                                   if Type.equals alpha beta then mua 
                                   else beta) a in
        min unfolded
  | Type.ZeroW | Type.SumW [] | Type.FunU(_, _, _) | Type.TensorU (_, _)
  | Type.BoxU(_,_) | Type.FunW (_, _) | Type.Link _->
      failwith "internal: min" 

(* If alpha <= beta then (embed alpha beta) is a corresponding 
 * embedding from alpha to beta.
 * The function raises Not_Leq if it discovers that alpha <= beta
 * does not hold.
 * *)
let rec embed (a: Type.t) (b: Type.t) : Term.t =
  if Type.equals a b then Term.mkLambdaW(("x", None), Term.mkVar "x")
  else 
    match Type.finddesc b with
    | Type.SumW[b1; b2] ->
        begin try 
          Term.mkLambdaW(("x", None), 
                         Term.mkInlW 
                           (Term.mkAppW (embed a b1) (Term.mkVar "x")))
        with Not_Leq ->
          Term.mkLambdaW(("x", None), 
                         Term.mkInrW 
                           (Term.mkAppW (embed a b2) (Term.mkVar "x")))
        end 
    | Type.TensorW(b1, b2) ->
        begin try 
          Term.mkLambdaW(("x", None), 
                         Term.mkPairW 
                           (Term.mkAppW (embed a b1) (Term.mkVar "x"))
                           (min b2))
        with Not_Leq ->
          Term.mkLambdaW(("x", None), 
                         Term.mkPairW 
                           (min b1)
                           (Term.mkAppW (embed a b2) (Term.mkVar "x")))
        end
    | Type.MuW(beta, b1) ->
        let mub1 = Type.newty (Type.MuW(beta, b1)) in
        let unfolded = 
          Type.subst (fun alpha -> if Type.equals alpha beta then mub1 else alpha) b1 in
          Term.mkLambdaW(("x", None),
                         Term.mkFoldW (beta,b1) (Term.mkAppW (embed a unfolded) (Term.mkVar "x")))
    | _ -> raise Not_Leq

(* If alpha <= beta then (embed alpha beta) is a corresponding 
 * embedding from beta to alpha. The functions (embed a b) and 
 * (project a b)form a section-retraction pair.
 * The function raises Not_Leq if it discovers that alpha <= beta
 * does not hold.
 * *)
let rec project (a: Type.t) (b: Type.t) : Term.t =
  if Type.equals a b then Term.mkLambdaW(("x", None), Term.mkVar "x")
  else 
    match Type.finddesc b with
    | Type.SumW[b1; b2] ->
        begin try 
          Term.mkLambdaW(
            ("x", None),
            Term.mkCaseW (Term.mkVar "x") 
              [("y", Term.mkAppW (project a b1) (Term.mkVar "y"));
               ("y", min a)])
        with Not_Leq ->
          Term.mkLambdaW(
            ("x", None),
            Term.mkCaseW (Term.mkVar "x") 
              [("y", min a);
               ("y", Term.mkAppW (project a b2) (Term.mkVar "y"))])
        end 
    | Type.TensorW(b1, b2) ->
        begin try 
          Term.mkLambdaW(("x", None), 
                         Term.mkLetW (Term.mkVar "x") 
                           (("y", "z"), 
                            Term.mkAppW (project a b1) (Term.mkVar "y")))
        with Not_Leq ->
          Term.mkLambdaW(("x", None), 
                         Term.mkLetW (Term.mkVar "x") 
                           (("y", "z"), 
                            Term.mkAppW (project a b2) (Term.mkVar "z")))
        end 
    | Type.MuW(beta, b1) ->
        let mub1 = Type.newty (Type.MuW(beta, b1)) in
        let unfolded = 
          Type.subst (fun alpha -> if Type.equals alpha beta then mub1 else alpha) b1 in
          Term.mkLambdaW(("x", None),
                         Term.mkAppW (project a unfolded) (Term.mkUnfoldW (beta,b1) (Term.mkVar "x")))
    | _ -> raise Not_Leq

type equation = int * (Term.var * Term.t)

let string_of_equation (i, (x, t)) =
  Printf.sprintf "and apply%i(%s) = %s" i x (Printing.string_of_termW t)

let eqns_of_circuit (c : circuit) : equation list =                                   
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
  let in_k k n t = 
    if k = 0 then t else Term.mkAppW (Term.mkVar (Printf.sprintf "apply%i" k)) t in
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
                             mkCaseW (mkVar x) 
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
            | Contr(w1 (* \Tens{A+B} X *), 
                    w2 (* \Tens A X *), 
                    w3 (* \Tens B X *)) when w1.src = dst  ->
                (x, mkLetW (mkVar x) ((sigma, v),
                  mkLetW (mkVar v) ((c, v),
                    mkCaseW (mkVar c) 
                         [(c, in_k w2.src (max_wire_src_dst + 1) 
                                (mkPairW (mkVar sigma) 
                                   (mkPairW (mkVar c) (mkVar v)))) ;
                          (d, in_k w3.src (max_wire_src_dst + 1) 
                                (mkPairW (mkVar sigma) 
                                   (mkPairW (mkVar d) (mkVar v)))) ]
                    )
                  )
                )
            | Contr(w1 (* \Tens{A+B} X *), 
                    w2 (* \Tens A X *), 
                    w3 (* \Tens B X *)) when w2.src = dst  ->
                (x, mkLetW (mkVar x) ((sigma, v), 
                  mkLetW (mkVar v) ((c, y),
                    in_k w1.src (max_wire_src_dst + 1) 
                      (mkPairW (mkVar sigma) 
                         (mkPairW (mkInlW (mkVar c)) (mkVar y)))
                  ) 
                ))
            | Contr(w1 (* \Tens{A+B} X *), 
                    w2 (* \Tens A X *), 
                    w3 (* \Tens B X *)) when w3.src = dst  ->
                (x, mkLetW (mkVar x) ((sigma, v),
                  mkLetW (mkVar v) ((d, y),
                    in_k w1.src (max_wire_src_dst + 1) 
                      (mkPairW (mkVar sigma) 
                         (mkPairW (mkInrW (mkVar d)) (mkVar y)))
                  ) 
                ))
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
                let a, b  = 
                  match Type.finddesc w1.type_back, 
                        Type.finddesc w2.type_forward with 
                    | Type.TensorW(a, _), Type.TensorW(b, _) -> a, b
                    | _ -> assert false in
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
                let a, b  = 
                  match Type.finddesc w1.type_forward, 
                        Type.finddesc w2.type_back with 
                    | Type.TensorW(a, _), Type.TensorW(b, _) -> a, b
                    | _ -> assert false in
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
                (* <sigma, <c, v>> @ w1 -> <sigma, v> @ w3 *)
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
              (x, mkConstW Cbot)
  in
  (* the term describing what happens to dart number k *)
  let rec part src wrs =
    match wrs with
      | [] -> 
            if 0 = src then
              (src, action c.output.src)
            else 
              let x = fresh_var () in 
                (src, (x, mkConstW Cbot))
      | w::rest ->
          if w.src = src then (src, action w.dst) else part src rest
  in
  let rec mkitoj i j = if i > j then [] else i :: (mkitoj (i+1) j) in
    (List.map (fun k -> part k all_wires) 
       (mkitoj 0 max_wire_src_dst))

let prg_of_circuit (c: circuit) : string =
  (* Rename the wires so that the output wire has label 0 *)
  let pi i = 
    if i = 0 then c.output.dst else if i = c.output.dst then 0 else i in 
  let c' = { output = map_wire pi c.output;
             instructions = List.map (map_instruction pi) c.instructions} in
  let eqns = eqns_of_circuit c' in
    "datatype ('a, 'b) sum = Inl of 'a | Inr of 'b \n" ^
    "val min = () \n" ^
    "val zero = 0 \n" ^
    "fun succ n = n + 1 \n" ^
    "fun pred n = if n > 0 then n-1 else n \n" ^
    "fun eq m n = if (m = n) then Inl() else Inr() \n" ^
    "fun listcase l = \n" ^
    "  case l of \n" ^
    "      [] => Inl() \n" ^
    "    | x::xs => Inr(x, xs) \n" ^
    "fun bot () = bot ()                  \n" ^
    "val nil = [] \n" ^
    "fun cons x xs = x :: xs  \n\n" ^
    "fun dummy () = 0 \n" ^ 
    (List.fold_left (fun s e -> (string_of_equation e) ^ "\n" ^ s) "" eqns)

let prg_termU (t: Term.t) : string =
  let graph = circuit_of_termU [] [] t in
  let _ = infer_types graph in 
    prg_of_circuit graph


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
                             mkCaseW (mkVar x) 
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
            | Contr(w1 (* \Tens{A+B} X *), 
                    w2 (* \Tens A X *), 
                    w3 (* \Tens B X *)) when w1.src = dst  ->
                (x, mkLetW (mkVar x) ((sigma, v),
                  mkLetW (mkVar v) ((c, v),
                    mkCaseW (mkVar c) 
                         [(c, in_k w2.src (max_wire_src_dst + 1) 
                                (mkPairW (mkVar sigma) 
                                   (mkPairW (mkVar c) (mkVar v)))) ;
                          (d, in_k w3.src (max_wire_src_dst + 1) 
                                (mkPairW (mkVar sigma) 
                                   (mkPairW (mkVar d) (mkVar v)))) ]
                    )
                  )
                )
            | Contr(w1 (* \Tens{A+B} X *), 
                    w2 (* \Tens A X *), 
                    w3 (* \Tens B X *)) when w2.src = dst  ->
                (x, mkLetW (mkVar x) ((sigma, v), 
                  mkLetW (mkVar v) ((c, y),
                    in_k w1.src (max_wire_src_dst + 1) 
                      (mkPairW (mkVar sigma) 
                         (mkPairW (mkInlW (mkVar c)) (mkVar y)))
                  ) 
                ))
            | Contr(w1 (* \Tens{A+B} X *), 
                    w2 (* \Tens A X *), 
                    w3 (* \Tens B X *)) when w3.src = dst  ->
                (x, mkLetW (mkVar x) ((sigma, v),
                  mkLetW (mkVar v) ((d, y),
                    in_k w1.src (max_wire_src_dst + 1) 
                      (mkPairW (mkVar sigma) 
                         (mkPairW (mkInrW (mkVar d)) (mkVar y)))
                  ) 
                ))
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
                let a = fst (unTensorW (snd (unTensorW w1.type_back))) in
                let b = fst (unTensorW (snd (unTensorW w2.type_forward))) in
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
                let a = fst (unTensorW (snd (unTensorW w1.type_forward))) in
                let b = fst (unTensorW (snd (unTensorW w2.type_back))) in
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
              (x, mkConstW Cbot)
  in
  (* the term describing what happens to dart number k *)
  let rec part src wrs =
    match wrs with
      | [] -> 
            if 0 = src then
              action c.output.src  
            else 
              let x = fresh_var () in 
                (x, mkConstW Cbot)
      | w::rest ->
          if w.src = src then action w.dst else part src rest
  in
  let rec whole =
    let x = fresh_var () in
    let y = fresh_var () in
    let rec mkitoj i j = if i > j then [] else i :: (mkitoj (i+1) j) in
    (x, mkCaseW (mkVar x) 
          [part 0 all_wires;
            (y, mkCaseW (mkVar y) 
                  (List.map (fun k -> part k all_wires) 
                     (mkitoj 1 max_wire_src_dst)))])
  in 
  let (x, w) = whole in
    mkLambdaW ((x, None), w)

let termW_of_circuit (c: circuit) : Term.t =
  (* Rename the wires so that the output wire has label 0 *)
  let pi i = 
    if i = 0 then c.output.dst else if i = c.output.dst then 0 else i in 
  let c' = { output = map_wire pi c.output;
             instructions = List.map (map_instruction pi) c.instructions} in
  let mp_term = message_passing_term c' in
  let compiled_term = mkTrW (mp_term) in 
    (* compiled_term has type 'a * X --> 'a * Y, we extract the X --> Y part.
     * Note: The compiled term is closed, so "x" cannot capture anything. *)
    mkLambdaW (("x", None),
               mkLetW (mkAppW compiled_term (mkPairW mkUnitW (mkVar "x")))
                 ((unusable_var, "x"), mkVar "x")
    )

let compile_termU (t: Term.t) : Term.t * Type.t =
(*  let t = Term.freshen_type_vars t in (* TODO: ??? *)*)
  let graph = circuit_of_termU [] [] t in
  let a = infer_types graph in 
  let compiled_term = termW_of_circuit graph in
(*  let a = principal_typeW [] compiled_term in *)
    (compiled_term, a)
