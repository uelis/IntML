(** Type inference
*)
open Term
open Term.Location
open Type
open Unify

(* Type substitutions *)
type contextW = (var * Type.t) list 
type contextU = (var * (Type.t * Type.t)) list 

type eqTag = 
  | ContextShape 
  | Boxed of Term.t 
  | ExpectedType of Term.t * (Type.t * Type.t) 

module U = Unify(struct type t = eqTag end)

(* Constraints *)
type type_constraint =
  | Eq of Type.t * Type.t * (eqTag option)
  | LEq of Type.t * Type.t

let eq_expected_constraint t (expected_ty, actual_ty) = 
  Eq (expected_ty, actual_ty, Some (ExpectedType(t, (expected_ty, actual_ty))))
let eq_tagged_constraint tag (t1, t2) = Eq (t1, t2, Some tag)
let eq_constraint e1 e2 = Eq (e1, e2, None)
let leq_constraint e1 e2 = LEq(e1, e2)

let string_of_constraint (c: type_constraint) =
  match c with
    | Eq (a, b, tag) ->
        (Printing.string_of_type a) ^ " = " ^ (Printing.string_of_type b)
    | LEq (a, b) ->
        (Printing.string_of_type a) ^ " <= " ^ (Printing.string_of_type b)

exception Typing_error of Term.t option * string                            

let rec fresh_tyVars n = 
  if n = 0 then [] 
  else (Type.newty Type.Var) :: (fresh_tyVars (n-1))    

(* A \cdot \Gamma *)
let rec dot (a : Type.t) (gamma: contextU) : contextU =
  match gamma with
    | [] -> []
    | (x, (b, ty)) :: rest ->         
        (x, (Type.newty (Type.TensorW(a, b)), ty)) :: (dot a rest)

(* Replace all index types in gamma with fresh type variables. *)
let rec fresh_index_types (gamma: contextU) : contextU =
  match gamma with
    | [] -> []
    | (x, (b, ty)) :: rest ->         
        let alpha = Type.newty Type.Var in 
        let gamma' = fresh_index_types rest in 
          (x, (alpha, ty)) :: gamma'

(* Compare the index-types point-wise. *)
let rec leq_index_types (gamma: contextU) (delta: contextU) 
      : type_constraint list =
  match gamma, delta with
    | [], [] -> []
    | (x, (a, _)) :: gamma', (y, (b, _)) :: delta' -> 
        (leq_constraint a b) :: (leq_index_types gamma' delta')
    | _ -> 
        failwith "geq_index_types must be called with contexts of same length"

let rec ptW (c: contextW) (t: Term.t) : Type.t * type_constraint list =
  match t.Term.desc with
  | Term.Var(v: var) ->
      begin try
        List.assoc v c, []
      with Not_found ->
        raise (Typing_error (Some t, " Variable '" ^ v ^ "' not bound.\n" ^
                             "Is it perhaps an upper class variable?"))
      end
  | ConstW(Cprint s) ->
      newty OneW, []
  | ConstW(Cintconst(_)) ->
      let intty = newty Type.NatW in
        intty, []
  | ConstW(Cintprint) ->
      let b = newty (FunW(newty Type.NatW, newty Type.OneW)) in
        b, []
  | ConstW(Cintadd) | ConstW(Cintsub) | ConstW(Cintmul) | ConstW(Cintdiv) ->
      let intty = newty Type.NatW in        
      let b = newty (FunW(intty, newty (FunW(intty, intty)))) in
        b, []
  | ConstW(Cinteq) | ConstW(Cintslt) ->
      let intty = newty NatW in
      let b = newty (FunW(intty, 
                          newty (FunW(intty, 
                                      newty (DataW(Data.boolid, [])))))) in
        b, []
  | ConstW(Cundef) ->
      let b = newty Var in
        b, []
  | UnitW ->
      newty OneW, []
  | PairW(t1, t2) ->
      let a1, con1 = ptW c t1 in
      let a2, con2 = ptW c t2 in
        newty (TensorW(a1, a2)), 
        con1 @ con2
  | LetW(t1, (x, y, t2)) ->
      if x = y then raise (Typing_error(Some t, "Duplicate variable in pattern.")) 
      else 
        let a1, con1 = ptW c t1 in
        let alpha, beta = newty Var, newty Var in
        let a2, con2 = ptW ([(x, alpha); (y, beta)] @ c) t2 in
          a2, 
          eq_expected_constraint t1 (a1, newty (TensorW(alpha, beta))) :: 
        con1 @ con2
  | InW(id, k, t1) ->
      let a1, con1 = ptW c t1 in
      let n = Data.params id in
      let params = fresh_tyVars n in
      let data = newty (DataW(id, params)) in
        (* TODO: check that constructor exists? *)
      let argtype = List.nth (Data.constructor_types id params) k in
      let fresh_data, fresh_argtype =
        match freshen_list [data; argtype] with
           | [fd; fa] -> fd, fa 
          | _ -> assert false in
        fresh_data,
        eq_expected_constraint t1 (a1, fresh_argtype) ::
        con1
  | CaseW(id, _, s, l) -> 
      let a1, con1 = ptW c s in
      let fresh_data, fresh_argtypes =
        let n = Data.params id in
        let params = fresh_tyVars n in
        let data = newty (DataW(id, params)) in
        let argtypes = Data.constructor_types id params in
          match freshen_list (data :: argtypes) with
            | fd :: fas -> fd, fas 
            | _ -> assert false in
      let beta = newty Var in
      let l_args = List.combine l fresh_argtypes in 
      let cons = List.fold_right 
                   (fun ((x, u), argty) cons -> 
                      let a2, con2 = ptW ((x, argty) :: c) u in
                        eq_expected_constraint u (a2, beta) :: con2 @ cons) 
                   l_args con1 in
        beta, 
        eq_expected_constraint s (a1, fresh_data) :: cons
  | AppW(s, t) ->
      let a1, con1 = ptW c s in
      let a2, con2 = ptW c t in
      let alpha = newty Var in
        alpha, 
        eq_expected_constraint s (a1, newty (FunW(a2, alpha))) :: 
        con1 @ con2
  | LambdaW((x, ty), t1) ->
      let alpha = newty Var in
      let a1, con1 = ptW ((x, alpha) :: c) t1 in
        newty (FunW(alpha, a1)), 
        begin match ty with
          | None -> con1
          | Some a-> eq_expected_constraint (Term.mkVar x) (alpha, a) :: con1
        end
  | AssignW(id, t1, t2) -> 
      if not (Type.Data.is_mutable id) then
        raise (Typing_error (Some t, "Assignment can only be used for mutable types."))
      else 
        let n = Data.params id in
        let params = fresh_tyVars n in
        let data = newty (DataW(id, params)) in
        let a1, con1 = ptW c t1 in
        let a2, con2 = ptW c t2 in
          newty OneW,
          eq_expected_constraint t1 (data, a1) ::
          eq_expected_constraint t2 (data, a2) ::
          con1 @ con2
  | LoopW(t1, (x, t2)) ->
      let a1, con1 = ptW c t1 in
      let alpha, beta = newty Var, newty Var in
      let a2, con2 = ptW ((x, alpha)::c) t2 in
        beta,
        eq_expected_constraint t2 (a2, newty (DataW(Data.sumid 2, [beta; a1]))) ::
        con1 @ con2
  | LetBoxW(t1, (xc, t2)) ->
      (* TODO: should allow t1 to appear in context c. 
       * (compilation is not implemented for this, though) *)
      let a1, con1 = ptU [] [] t1 in
      let alpha = newty Var in
      let a2, con2 = ptW ((xc, alpha)::c) t2 in
        a2,
        eq_expected_constraint t1 (a1, newty (BoxU(newty OneW, alpha))) ::
        con1 @ con2
  | Term.ContW(i, n, t) ->
      let _, con = ptW c t in
      let alpha = newty Var in
        newty (ContW(alpha)),
        con
          (* TODO: this is underspecified!?! *)
  | Term.CallW(fn, t) ->
      let _, con = ptW c t in
      let alpha = newty Var in
        alpha,
        con
          (* TODO : unsafe *)
  | TypeAnnot(t, None) -> 
      ptW c t
  | TypeAnnot(t, Some ty) ->
      let a, con = ptW c t in
        a,
        eq_expected_constraint t (a, ty) :: con
  | PairU(_, _) | LetU(_, _) | AppU(_, _) | LambdaU(_, _) | BoxTermU(_)
  | LetBoxU(_, _) | CaseU(_, _, _) | CopyU(_, _) | HackU(_, _) | MemoU(_)
  | SuspendU _ | ForceU _ | ExternalU _->
      raise (Typing_error (Some t, "Working class term expected."))
and ptU (c: contextW) (phi: contextU) (t: Term.t) 
        : Type.t * type_constraint list =
  match t.Term.desc with
  | Term.Var(v) ->
      begin try
        let (tyW, tyX) = List.assoc v phi in 
          tyX,
          [leq_constraint (newty OneW) tyW]
      with Not_found ->
        let msg = 
          if List.mem_assoc v c then
            "Variable '" ^ v ^ "' is a working class variable,\n" ^
            "not an upper class one, as expected.\n"
          else 
            "Variable '" ^ v ^ "' not bound.\n" ^
            "This could happen if it has been used elsewhere\n" ^
            "and is thus not available anymore because of linearity."
        in raise (Typing_error (Some t, msg))
      end
  | PairU(s, t) ->
      let fv_s = Term.free_vars s in
      let fv_t = Term.free_vars t in
      let gamma = 
        List.filter (fun (x,a) -> List.mem x fv_s) phi in
      let delta = 
        List.filter (fun (x,a) -> (List.mem x fv_t) && 
                                  (not (List.mem x fv_s))) phi in
      let tyX, conX = ptU c gamma s in
      let tyY, conY = ptU c delta t in
        newty (TensorU(tyX, tyY)),
        conX @ conY
  | LetU(s, (x, y, t)) ->
      if x = y then raise (Typing_error(Some t, "Duplicate variable in pattern.")) 
      else 
        let fv_s = Term.free_vars s in
        let fv_t = List.filter (fun z -> z <> x && z <> y) (Term.free_vars t) in
        let banged_gamma = 
          List.filter (fun (x,a) -> List.mem x fv_s) phi in
        let delta = 
          List.filter (fun (z,a) -> (List.mem z fv_t) && 
                                    (not (List.mem z fv_s))) phi in        
        let alpha, beta1, beta2 = newty Var, newty Var, newty Var in
        let tZ, conZ = ptU c ([(x, (alpha, beta1)); 
                               (y, (alpha, beta2))] @ delta) t in
        let gamma = fresh_index_types banged_gamma in
        let conC = leq_index_types (dot alpha gamma) banged_gamma in
        let tyXY, conXY = ptU c gamma s in
          tZ, 
          eq_expected_constraint s 
            (tyXY, newty (TensorU(beta1, beta2))) :: 
          conXY @ conC @ conZ
  | AppU(s, t) ->
      let fv_s = Term.free_vars s in
      let fv_t = Term.free_vars t in
      let gamma = 
        List.filter (fun (x,a) -> List.mem x fv_s) phi in
      let banged_delta = 
        List.filter (fun (x,a) -> (List.mem x fv_t) && 
                                  (not (List.mem x fv_s))) phi in        
      let tyFun, conFun = ptU c gamma s in
      let alpha, betaY = newty Var, newty Var in
      let delta = fresh_index_types banged_delta in
      let conC = leq_index_types (dot alpha delta) banged_delta in
      let tyX, conX = ptU c delta t in
        betaY,
        eq_expected_constraint s
          (tyFun, newty (FunU(alpha, tyX, betaY))) ::
        conFun @ conC @ conX
  | LambdaU((x, ann), t) ->
      let alpha, beta = newty Var, newty Var in
      let tyY, conY = ptU c ((x, (alpha, beta)) :: phi) t in
      let conAnn =
        match ann with 
          | None -> []
          | Some tyX -> [eq_expected_constraint (Term.mkVar x) 
                           (beta, tyX)]
      in 
        newty (FunU(alpha, beta, tyY)),
        (conY @ conAnn)
  | CopyU(s, (x, y, t)) ->
      let fv_s = Term.free_vars s in
      let fv_t = List.filter (fun z -> z <> x && z <> y) (Term.free_vars t) in
      let banged_gamma = 
        List.filter (fun (x,a) -> List.mem x fv_s) phi in
      let delta = 
        List.filter (fun (z,a) -> (List.mem z fv_t) && 
                                  (not (List.mem z fv_s))) phi in        
      let alpha1, alpha2, beta = newty Var, newty Var, newty Var in
      let tyY, conY = ptU c ([(x, (alpha1, beta)); 
                              (y, (alpha2, beta))] @ 
                             delta) 
                        t in
      let gamma = fresh_index_types banged_gamma in
      let conC = leq_index_types 
                   (dot (newty (DataW(Data.sumid 2, [alpha1; alpha2]))) gamma) 
                   banged_gamma in
      let tyX, conX = ptU c gamma s in
        tyY,
        eq_expected_constraint s (tyX, beta) ::
        conX @ conC @ conY
  | CaseU(id, s, l) -> 
      let a1, con1 = ptW c s in
        (* TODO: appears twice *)
      let fresh_data, fresh_argtypes =
        let n = Data.params id in
        let params = fresh_tyVars n in
        let data = newty (DataW(id, params)) in
        let argtypes = Data.constructor_types id params in
          match freshen_list (data :: argtypes) with
            | fd :: fas -> fd, fas 
            | _ -> assert false in
      let beta = newty Var in
      let l_args = List.combine l fresh_argtypes in 
      let cons = List.fold_right 
                   (fun ((x, u), argty) cons -> 
                      let a2, con2 = ptU ((x, argty) :: c) phi u in
                        eq_expected_constraint u (a2, beta) :: con2 @ cons) 
                   l_args con1 in
        beta, 
        eq_expected_constraint s (a1, fresh_data) :: cons
  | BoxTermU(f) ->
      let tyW, con = ptW c f in
        newty (BoxU(newty OneW, tyW)), 
        con
  | LetBoxU(s, (xc, t)) ->
      let fv_s = Term.free_vars s in
      let fv_t = Term.free_vars t in
      let gamma = 
        List.filter (fun (x,a) -> List.mem x fv_s) phi in
      let banged_delta = 
        List.filter (fun (x,a) -> (List.mem x fv_t) && 
                                  (not (List.mem x fv_s))) phi in       
      let tyBox, conBox = ptU c gamma s in
      let alpha = newty Var in
      let delta = fresh_index_types banged_delta in
      let conC = leq_index_types (dot (alpha) delta) banged_delta in
      let tyB, conB = ptU ((xc, alpha) :: c) delta t in
      let beta = newty Var in
        tyB,
        eq_expected_constraint s (tyBox, newty (BoxU(newty OneW, alpha))) :: 
        eq_tagged_constraint (Boxed t) (tyB, newty (BoxU(newty OneW, beta))) ::
        conC @ conBox @ conB
  | HackU(None, t1) ->
      failwith "ptU cannot be applied to unannotated Hack!"
  | HackU(Some b, t1) ->
      let a1, con1 = ptW c t1 in
      let (b_minus, b_plus) = Type.question_answer_pair (Type.freshen_index_types b) in
          (* TODO
          (fun beta -> 
             raise (Typing_error ("Type annotations on hack must not " ^
                                  " contain type variables!")))
           *)
        (b, 
         eq_expected_constraint t (newty (FunW(b_minus, b_plus)), a1) ::
         con1)
  | MemoU(t1) ->
      ptU [] [] t1
  | ExternalU(fn, ty) ->
      Type.freshen ty, []
  | SuspendU(t) ->
      let gamma = fresh_index_types phi in
      let tyBox, conBox = ptU c gamma t in
      let alpha = newty Var in
      let cont = newty (ContW alpha) in
      let contcont = newty (ContW cont) in
      let conC = leq_index_types (dot cont gamma) phi in
      let b = newty (BoxU(newty OneW, contcont)) in
        b,
        eq_expected_constraint t (tyBox, newty (BoxU(newty OneW, alpha))) :: 
        conC @ conBox 
  | ForceU(t) ->
      let tyK, conK = ptW c t in
      let alpha = newty Var in
      let cont = newty (ContW alpha) in
      let contcont = newty (ContW cont) in
      let b = newty (BoxU(newty OneW, alpha)) in
        b,
        eq_expected_constraint t (tyK, contcont) :: 
        conK 
  | TypeAnnot(t, None) -> 
      ptU c phi t
  | TypeAnnot(t, Some ty) ->
      let a, con = ptU c phi t in
        a,
        eq_expected_constraint t (a, ty) :: con
  | LoopW _  |LambdaW (_, _) | AppW (_, _) | CaseW _ | InW (_, _, _) 
  | LetW (_, _) | LetBoxW(_,_) | PairW (_, _) | ConstW (_) | UnitW 
  | AssignW _ | Term.ContW _ | CallW _ ->
      raise (Typing_error (Some t, "Upper class term expected."))

let raise_error (failed_eqn: U.failure_reason) =
  match failed_eqn with
    | U.Cyclic_type(t, _, Some (ExpectedType(s, _)))
    | U.Cyclic_type(t, _, Some (Boxed(s))) ->
        let msg = "Term has cyclic type " ^
                  (Printing.string_of_type t) ^ "." in
          raise (Typing_error(Some(s), msg))
    | U.Cyclic_type(t, _, Some ContextShape)
    | U.Cyclic_type(t, _, None) ->
        let msg = "Unification leads to cyclic type " ^
                  (Printing.string_of_type t) ^ "." in
          raise (Typing_error(None, msg))
    | U.Equation_failed(_, _, Some (ExpectedType(s, (tys, expected)))) ->
        let msg = "Term should have the type " ^ 
                  (Printing.string_of_type expected) ^ 
                  ", but has type " ^ 
                  (Printing.string_of_type tys) ^ "." in
          raise (Typing_error (Some s, msg))
    | U.Equation_failed(tys, expected, Some(Boxed(s))) ->
        let msg = "Term has type " ^ 
                  (Printing.string_of_type tys) ^ ", " ^ 
                  "but it it expected to have a boxed type." in
          raise (Typing_error (Some s, msg))
    | U.Equation_failed(tys, tyt, Some(ContextShape)) ->
        let msg = "Constraints on the context shape cannot be satisfied. " ^
                  "Cannot unify " ^ 
                  (Printing.string_of_type tys) ^ 
                  " with " ^ 
                  (Printing.string_of_type tyt) ^ "." in
          raise (Typing_error (None, msg))
    | U.Equation_failed(_, _, None) ->
        let msg = "Cannot unify." in
          raise (Typing_error(None, msg))

let solve_constraints (con: type_constraint list) : unit =
  (* separate context in inequalities and equalities *)
  let rec separate con ineqs eqs = 
    begin
      match con with
        | [] -> ineqs, eqs
        | LEq(t, t') :: con' ->
            separate con' ((t, t') :: ineqs) eqs
        | Eq(t, t', tag) :: con' ->
            separate con' ineqs  ((t, t', tag) :: eqs)
    end in
  let ineqs, eqs = separate con [] [] in
  (* unify equations first *)
  U.unify_pairs eqs;
  (* All inequalities have the form A <= alpha for some variable alpha.
   * Compute now for each variable a single lower bound that subsumes all
   * given inequations. The result maps each variable to a lower bound. *)
  let m = Type.Typetbl.create 10 in
  let rec join_lower_bounds (ineqs: (Type.t * Type.t) list) : unit = 
    (*
    Printf.printf "---\n";
    List.iter (fun (a,b) -> Printf.printf "%s <= %s\n" 
                              (Printing.string_of_type a)
                              (Printing.string_of_type b)) ineqs;
    Printf.printf "===\n";
     *)
    match ineqs with
      | [] -> ()
      | (a, alpha) :: rest ->
          let b = 
            try a :: Type.Typetbl.find m (Type.find alpha) with Not_found -> [a]
(*              newty (DataW(Data.sumid 2, [a; Type.Typetbl.find m (Type.find
 *              alpha)])) with Not_found -> a *)
          in
            Type.Typetbl.replace m (Type.find alpha) b;
            join_lower_bounds rest in
  let fresh_ty = Vargen.mkVarGenerator "recty" ~avoid:[] in
  let solve_ineq (a, alpha) =
    assert (Type.finddesc alpha = Var);
    let fva = Type.free_vars a in
    let sol = 
      if List.exists (fun beta -> find beta == find alpha) fva then
        begin
          let recty =fresh_ty () in
          let n = List.length fva in
            Type.Data.make recty n;
            Type.Data.add_constructor recty ("con" ^ recty) fva a;
            newty (DataW(recty, fva))
        end
      else 
        a in
        (*
    let sol =
      if List.exists (fun beta -> find beta == find alpha) fva then
        let beta = newty Var in
        let a' = subst (fun x -> if equals x alpha then beta else x) a in
(*        Type.newty (Type.MuW(beta, Type.newty (Type.SumW [Type.newty Type.OneW; a']))) *)
          Type.newty (Type.MuW(beta, a')) 
      else 
        a in*)
      U.unify_pairs [sol, alpha, Some ContextShape]
  in
    join_lower_bounds ineqs;
    (* Add equations for lower bounds. *)    
    let ineqs = 
      Type.Typetbl.fold (fun alpha a l -> 
                           match a with
                             | [a0] -> (a0, alpha) :: l
                             | _ -> (newty (DataW(Data.sumid (List.length a), a)), alpha) :: l)
        m [] 
    in
    (*
    Printf.printf "---\n";
    List.iter (fun (a,b) -> Printf.printf "%s <= %s\n" 
                              (Printing.string_of_type a)
                              (Printing.string_of_type b)) ineqs;
    Printf.printf "===\n";
     *)
      List.iter solve_ineq ineqs
      (*
  List.iter (fun (t, t', _) ->
               Printf.printf "%s = %s\n" 
                 (Printing.string_of_type t)
                 (Printing.string_of_type t')) eqs_of_ineqs;
  flush stdout; *)

exception Not_Leq               

(* If alpha <= beta then (embed alpha beta) is a corresponding 
 * embedding from alpha to beta.
 * The function raises Not_Leq if it discovers that alpha <= beta
 * does not hold.
 * *)
let embed (a: Type.t) (b: Type.t) : Term.t =
  if Type.equals a b then Term.mkLambdaW(("x", None), Term.mkVar "x")
  else 
    match Type.finddesc b with
      | Type.DataW(id, l) ->
          let cs = Type.Data.constructor_types id l in
          let rec inject l n =
            match l with 
              | [] -> raise Not_Leq
              | b1 :: bs ->
                  if Type.equals a b1 then
                    Term.mkLambdaW(("x", None), Term.mkInW id n (Term.mkVar "x"))
                  else 
                    inject bs (n + 1) in
            inject cs 0
      | _ -> raise Not_Leq

(* If alpha <= beta then (embed alpha beta) is a corresponding 
 * embedding from beta to alpha. The functions (embed a b) and 
 * (project a b)form a section-retraction pair.
 * The function raises Not_Leq if it discovers that alpha <= beta
 * does not hold.
 * *)
let project (a: Type.t) (b: Type.t) : Term.t =            
  if Type.equals a b then 
    Term.mkLambdaW(("x", None), Term.mkVar "x")
  else 
    match Type.finddesc b with
      | Type.DataW(id, l) ->
          let cs = Type.Data.constructor_types id l in
          let rec out l n =
            match l with 
              | [] -> raise Not_Leq
              | b1 :: bs ->
                  if Type.equals a b1 then
                    Term.mkLambdaW(
                      ("x", None),
                      Term.mkCaseW id true (Term.mkVar "x") 
                        (Listutil.init (List.length cs)
                           (fun j-> 
                              if j = n then 
                                ("y", Term.mkVar "y")
                              else
                                (unusable_var, mkConstW Cundef))))
                  else
                    out bs (n + 1) in
            out l 0
    | _ -> 
        raise Not_Leq 


let principal_typeW (c: contextW) (t: Term.t) : Type.t = 
  try 
    let a, con = ptW c t in
      solve_constraints con;
      a
  with 
    | U.Not_Unifiable failed_cnstrnt -> raise_error failed_cnstrnt

let principal_typeU (c: contextW) (phi: contextU) (t: Term.t) : Type.t = 
  try
    let tyX, con = ptU c phi t in
      solve_constraints con;
      tyX
  with 
    | U.Not_Unifiable failed_cnstrnt -> raise_error failed_cnstrnt
