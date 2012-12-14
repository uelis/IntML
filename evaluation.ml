(** Evaluation of working class terms.
  *)
open Term

(* evaluation of closed terms *)  

type env = (var * value) list
and value =
  | NatPredV 
  | IntV of int
  | UnitV 
  | InV of int * int * value
  | PairV of value * value
  | FunV of env * var * Term.t
  | InteqV of value option
  | IntsltV of value option
  | IntaddV of value option
  | IntsubV of value option
  | IntmulV of value option
  | IntdivV of value option
  | IntprintV

let rec cv2termW (v: value) : Term.t =
  match v with 
    | UnitV -> mkUnitW 
    | IntV(i) -> mkConstW (Cintconst(i))
    | InV(n, i, v1) -> mkInW n i (cv2termW v1)
    | PairV(v1, v2) -> mkPairW (cv2termW v1) (cv2termW v2)
(*    | FoldV((alpha, a), v) -> mkFoldW (alpha, a) (cv2termW v) *)
    | _ -> assert false

let newid =
  let n = ref 0 in
    fun () -> n := !n + 1; !n

let heap = Hashtbl.create 2

exception Not_Leq               

(* If alpha <= beta then (embed alpha beta) is a corresponding 
 * embedding from alpha to beta.
 * The function raises Not_Leq if it discovers that alpha <= beta
 * does not hold.
 * *)
let embed (a: Type.t) (b: Type.t) : Term.t =
let rec embed i (a: Type.t) (b: Type.t) : Term.t =
  if i > 1 then raise Not_Leq;
  if Type.equals a b then Term.mkLambdaW(("x", None), Term.mkVar "x")
  else 
    match Type.finddesc b with
    | Type.SumW[b1; b2] ->
        begin try 
          Term.mkLambdaW(("x", None), 
                         Term.mkInlW 
                           (Term.mkAppW (embed i a b1) (Term.mkVar "x")))
        with Not_Leq ->
          Term.mkLambdaW(("x", None), 
                         Term.mkInrW 
                           (Term.mkAppW (embed i a b2) (Term.mkVar "x")))
        end 
    | Type.TensorW(b1, b2) ->
        raise Not_Leq
(*        begin try 
          Term.mkLambdaW(("x", None), 
                         Term.mkPairW 
                           (Term.mkAppW (embed i a b1) (Term.mkVar "x"))
                           (min b2))
        with Not_Leq ->
          Term.mkLambdaW(("x", None), 
                         Term.mkPairW 
                           (min b1)
                           (Term.mkAppW (embed i a b2) (Term.mkVar "x")))
        end*)
    | Type.MuW(beta, b1) ->
        let mub1 = Type.newty (Type.MuW(beta, b1)) in
        let unfolded = 
          Type.subst (fun alpha -> if Type.equals alpha beta then mub1 else alpha) b1 in
          Term.mkLambdaW(("x", None),
                         Term.mkFoldW (beta,b1) (Term.mkAppW (embed (i+1) a unfolded) (Term.mkVar "x")))
    | _ -> raise Not_Leq
             in
  embed 0 a b

(* If alpha <= beta then (embed alpha beta) is a corresponding 
 * embedding from beta to alpha. The functions (embed a b) and 
 * (project a b)form a section-retraction pair.
 * The function raises Not_Leq if it discovers that alpha <= beta
 * does not hold.
 * *)
let project (a0: Type.t) (b0: Type.t) : Term.t =            
let rec project i (a: Type.t) (b: Type.t) : Term.t =
  if i > 1 then raise Not_Leq;
  if Type.equals a b then Term.mkLambdaW(("x", None), Term.mkVar "x")
  else 
    match Type.finddesc b with
    | Type.SumW[b1; b2] ->
        begin try 
          Term.mkLambdaW(
            ("x", None),
            Term.mkCaseW (Term.mkVar "x") 
              [("y", Term.mkAppW (project i a b1) (Term.mkVar "y"));
               (unusable_var, mkConstW Cundef)])
        with Not_Leq ->
          Term.mkLambdaW(
            ("x", None),
            Term.mkCaseW (Term.mkVar "x") 
              [(unusable_var,  mkConstW Cundef);
               ("y", Term.mkAppW (project i a b2) (Term.mkVar "y"))])
        end 
(*    | Type.TensorW(b1, b2) ->
        begin try 
          Term.mkLambdaW(("x", None), 
                         Term.mkLetW (Term.mkVar "x") 
                           (("y", "z"), 
                            Term.mkAppW (project i a b1) (Term.mkVar "y")))
        with Not_Leq ->
          Term.mkLambdaW(("x", None), 
                         Term.mkLetW (Term.mkVar "x") 
                           (("y", "z"), 
                            Term.mkAppW (project i a b2) (Term.mkVar "z")))
        end *)
    | Type.MuW(beta, b1) ->
        let mub1 = Type.newty (Type.MuW(beta, b1)) in
        let unfolded = 
          Type.subst (fun alpha -> if Type.equals alpha beta then mub1 else alpha) b1 in
          Term.mkLambdaW(("x", None),
                         Term.mkLetCompW
                           (Term.mkAppW (project (i+1) a unfolded) (Term.mkUnfoldW (beta,b1) (Term.mkVar "x")))
                           ("y", Term.mkLetCompW
                                   (Term.mkDeleteW (beta,b1) (Term.mkVar "x"))
                                   (unusable_var, Term.mkVar "y")))
    | _ -> 
        raise Not_Leq in
  try
  project 0 a0 b0
  with Not_Leq ->
        Printf.printf "%s | %s \n" (Printing.string_of_type a0)(Printing.string_of_type b0);
        flush stdout;
        raise Not_Leq 

let rec eval (t: Term.t) (sigma : env) : value =
(*  Printf.printf "%s\n\n" (Printing.string_of_termW t);  *)
  match t.desc with 
    | Var(x) -> List.assoc x sigma
    | UnitW -> UnitV 
    | ConstW(Cprint s) -> 
        print_string s;
        flush stdout;
        UnitV
    | ConstW(Cintconst(i)) -> IntV(i)
    | ConstW(Cintprint) -> IntprintV
    | ConstW(Cinteq) -> InteqV(None)
    | ConstW(Cintslt) -> IntsltV(None)
    | ConstW(Cintadd) -> IntaddV(None)
    | ConstW(Cintsub) -> IntsubV(None)
    | ConstW(Cintmul) -> IntmulV(None)
    | ConstW(Cintdiv) -> IntdivV(None)
    | ConstW(Cundef) ->  failwith "undefined!"
    | PairW(t1, t2) -> 
        let v1 = eval t1 sigma in
        let v2 = eval t2 sigma in
        PairV(v1, v2)
    | LetW(t1, (x1, x2, t2)) ->
       (match eval t1 sigma with
        | PairV(v1, v2) -> eval t2 ((x1, v1) :: (x2, v2) :: sigma)
        | _ -> failwith (Printf.sprintf "Internal: Pairs (%s)" (Printing.string_of_termW t))
       )
    | InW(n, i, t1) -> InV(n, i, eval t1 sigma)
    | CaseW(t1, l) ->
       (match eval t1 sigma with
          | InV(n, i, v1) -> 
              let (x2, t2) = List.nth l i in
                eval t2 ((x2, v1) :: sigma)
          | _ -> failwith "Internal: Case distinction"
       )
    | AppW(t1, t2) -> 
        let v1 = eval t1 sigma in
        let v2 = eval t2 sigma in
          appV v1 v2
    | LambdaW((x, _), t1) -> FunV(sigma, x, t1)
    | LoopW(t1, (x, t2)) ->
        let v1 = eval t1 sigma in
        let rec loop v = 
          match eval t2 ((x, v) :: sigma) with
            | InV(2, 0, v2) -> v2
            | InV(2, 1, v2) -> loop v2
            | _ -> failwith "Internal: evaluation of loop" in
          loop v1
    | FoldW((alpha, a), t) ->
        let id = newid () in
        let v = eval t sigma in
          Hashtbl.replace heap id v; 
          IntV id
    | UnfoldW(_, t) ->
        (match eval t sigma with
           | IntV id -> 
               (try Hashtbl.find heap id with 
                 | Not_found -> failwith "Internal: unfold applied to a deallocated value.")
           | _ -> assert false)
    | AssignW((alpha, a), s, t) ->
        let vs = eval s sigma in
        let vt = eval t sigma in
        (match vs with
           | IntV id -> Hashtbl.replace heap id vt;
                        UnitV
           | _ -> assert false)
    | DeleteW((alpha, a), s) ->
        let vs = eval s sigma in
        (match vs with
           | IntV id -> Hashtbl.remove heap id;
                        UnitV
           | _ -> assert false)
    | EmbedW((a, b), s) ->
          eval (mkAppW (embed a b) s) sigma
    | ProjectW((a, b), s) ->
          eval (mkAppW (project a b) s) sigma
    | ContW(i, n, s) ->
        eval (Compile.in_k i n s) sigma           
    | LetBoxW(t1, (x, t2)) ->
        let s1, a1 = Compile.compile_termU t1 in
        let v1 = eval (mkAppW s1 mkUnitW) sigma in
          eval t2 ((x, v1) :: sigma)
    | TypeAnnot(t, _) -> eval t sigma
    | HackU (_, _)|CopyU (_, _)|CaseU (_, _, _)|LetBoxU (_, _)|BoxTermU _
    | LambdaU (_, _)|AppU (_, _)|LetU (_, _)|PairU (_, _) | MemoU(_)
    | ForceU _ | SuspendU _
      -> assert false

and appV (v1: value) (v2: value) : value = 
  match v1 with
    | FunV(tau, x, t1) -> eval t1 ((x, v2) :: tau)
    | NatPredV -> 
        begin
          match v2 with
            | IntV(n) -> if n > 0 then IntV(n-1) else IntV(n)
            | _ -> failwith "Internal: wrong application of pred"
        end
    | InteqV(None) -> InteqV(Some v2)
    | InteqV(Some v3) -> 
        (match v3, v2 with
           | IntV(v3'), IntV(v2') -> 
               if v3' = v2' then InV(2, 0, UnitV) else InV(2, 1, UnitV)
           | _ -> assert false)
    | IntsltV(None) -> IntsltV(Some v2)
    | IntsltV(Some v3) -> 
        (match v3, v2 with
           | IntV(v3'), IntV(v2') -> 
               if v3' < v2' then InV(2, 0, UnitV) else InV(2, 1, UnitV)
           | _ -> assert false)
    | IntaddV(None) -> IntaddV(Some v2)
    | IntaddV(Some v3) -> 
        (match v2, v3 with
           | IntV(v2'), IntV(v3') -> IntV(v3' + v2')
           | _ -> assert false)
    | IntsubV(None) -> IntsubV(Some v2)
    | IntsubV(Some v3) -> 
        (match v2, v3 with
           | IntV(v2'), IntV(v3') -> IntV(v3' - v2')
           | _ -> assert false)
    | IntmulV(None) -> IntmulV(Some v2)
    | IntmulV(Some v3) -> 
        (match v2, v3 with
           | IntV(v2'), IntV(v3') -> IntV(v3' * v2')
           | _ -> assert false)
    | IntdivV(None) -> IntdivV(Some v2)
    | IntdivV(Some v3) ->
        (match v2, v3 with
           | IntV(v2'), IntV(v3') -> IntV(v3' / v2')
           | _ -> assert false)
    | IntprintV ->
        (match v2 with
           | IntV(v2') -> Printf.printf "%i" v2'; UnitV
           | _ -> assert false)
    | _ -> failwith "Internal: Cannot apply non-functional value."

exception FunctionalValue

let eval_closed (t: Term.t) : Term.t option =
  let rec cv2termW (v: value) =
    match v with 
      | UnitV -> mkUnitW 
      | IntV(i) -> mkConstW (Cintconst(i))
      | InV(n, i, v1) -> mkInW n i (cv2termW v1)
      | PairV(v1, v2) -> mkPairW (cv2termW v1) (cv2termW v2)
(*     | FoldV((alpha, a), v) -> mkFoldW (alpha, a) (cv2termW v) *)
      | _ -> raise FunctionalValue in    
  let v = eval t [] in
    try 
      Some (cv2termW v)
    with 
      | FunctionalValue -> None
