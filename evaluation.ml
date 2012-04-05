(** Evaluation of working class terms.
  *)
open Term

(* evaluation of closed terms *)  

type env = (var * value) list
and value =
  | NatPredV 
  | NilV 
  | ConsV of (value option) * (value option)
  | MatchV
  | NatV of int
  | UnitV 
  | SuccV of Type.t
  | EqV of Type.t * value option
  | InV of int * int * value
  | PairV of value * value
  | FunV of env * var * Term.t
  | TrV of env * var * Term.t
  | LoopV of env * var * Term.t

let rec min (ty: Type.t) =
  match Type.finddesc ty with
  | Type.Var -> 
      Printf.printf "warning: trying to evaluate polymophic min; instantiating variables with 1\n";
      UnitV  
  | Type.NatW -> NatV(0)
  | Type.OneW -> UnitV
  | Type.TensorW(a, b) -> PairV(min a, min b)
  | Type.SumW(a :: l) -> InV(1 + (List.length l), 0, min a)
  | Type.ZeroW | Type.SumW [] | Type.FunU(_, _, _) | Type.TensorU (_, _)
  | Type.BoxU(_,_) | Type.FunW (_, _) | Type.Link _ | Type.ListW _ ->
      failwith "internal: min" 

type succOrMin =
  | Succ of value
  | Min of value

let rec succmin (ty: Type.t) (v: value) : succOrMin =
  match Type.finddesc ty, v with
  | Type.Var, _ -> 
      Printf.printf "warning: trying to evaluate polymophic succ; instantiating variables with 1\n";
      Min(UnitV)  
  | Type.NatW, NatV(n) -> Succ(NatV(n+1))
  | Type.OneW, _ -> Min(UnitV)
  | Type.TensorW(a, b), PairV(x, y) -> 
     (match succmin b y with
      | Succ(y') -> Succ(PairV(x, y'))
      | Min(mb) -> 
        (match succmin a x with
         | Succ(x') -> Succ(PairV(x', mb))
         | Min(ma) -> Min(PairV(ma, mb))
        )
     )
  | Type.SumW(l), InV(n, i, x) ->
     (match succmin (List.nth l i) x with
      | Succ(x') -> Succ(InV(n, i, x'))
      | Min(_) -> if (i < n - 1) then 
                     Succ(InV(n, i + 1, min (List.nth l (i+1)))) 
                  else Min(min (Type.find ty))
     )
  | _, _ -> 
     Printf.printf "%s" (Printing.string_of_type ty);
     failwith "internal: succmin"

let rec eq (ty: Type.t) (v1: value) (v2: value) : bool =
  match Type.finddesc ty, v1, v2 with
  | Type.Var, _, _ -> 
      Printf.printf "warning: trying to evaluate polymophic eq; instantiating variables with 1\n";
      true
  | Type.OneW, _, _ -> true
  | Type.NatW, NatV(v), NatV(w) -> v=w
  | Type.TensorW(a, b), PairV(v11, v12), PairV(v21, v22) -> eq a v11 v21 && eq b v12 v22
  | Type.SumW(l), InV(m, i, v1'), InV(n, j, v2') -> 
         (m = n) && (i = j) && (eq (List.nth l i) v1' v2')
  | _ -> false

let rec eval (t: Term.t) (sigma : env) : value =
  match t.desc with 
    | Var(x) -> List.assoc x sigma
    | UnitW -> UnitV 
    | ConstW(_, Cprint s) -> 
        print_string s;
        flush stdout;
        UnitV
    | ConstW(Some a, Cnatpred) -> NatPredV
    | ConstW(Some a, Cnil) -> NilV
    | ConstW(Some a, Ccons) -> ConsV(None, None)
    | ConstW(Some a, Clistcase) -> MatchV
    | ConstW(Some a, Cmin) -> min a
    | ConstW(Some a, Csucc) -> 
        begin 
          match Type.finddesc a with
            | Type.FunW(b, _) -> SuccV(b)
            | _ -> assert false
        end
    | ConstW(Some a, Ceq) -> 
        begin 
          match Type.finddesc a with
            | Type.FunW(b, _) -> EqV(b, None)
            | _ -> assert false
        end
    | ConstW(_, Cbot) ->  failwith "nontermination!"
      (* Note: "bot" does not need to be annotated *)
    | ConstW(None, s) ->
        failwith ("Cannot evaluate unannotated constant '" ^ (Printing.string_of_term_const s) ^ "'.")
    | PairW(t1, t2) -> 
        let v1 = eval t1 sigma in
        let v2 = eval t2 sigma in
        PairV(v1, v2)
    | LetW(t1, (x1, x2, t2)) ->
       (match eval t1 sigma with
        | PairV(v1, v2) -> eval t2 ((x1, v1) :: (x2, v2) :: sigma)
        | _ -> failwith "Internal: Pairs"
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
    | LambdaW((x, _), t1) ->   FunV(sigma, x, t1)
    | TrW(t1) ->
       (match eval t1 sigma with
        | FunV(tau, x, t1) -> TrV(tau, x, t1)
        | _ -> failwith "Internal: Wrong application of trace."
       )
    | LetBoxW(t1, (x, t2)) ->
        let s1, a1 = Compile.compile_termU t1 in
        let v1 = eval (mkAppW s1 mkUnitW) sigma in
          eval t2 ((x, v1) :: sigma)
    | TypeAnnot(t, _) -> eval t sigma
    | HackU (_, _)|CopyU (_, _)|CaseU (_, _, _)|LetBoxU (_, _)|BoxTermU _
    | LambdaU (_, _)|AppU (_, _)|LetU (_, _)|PairU (_, _)
      -> assert false

and appV (v1: value) (v2: value) : value =
  match v1 with
    | FunV(tau, x, t1) -> eval t1 ((x, v2) :: tau)
    | TrV(tau, x, t1) -> appV (LoopV(tau, x, t1)) (InV(2, 0, v2))
    | LoopV(tau, x, t1) ->     
      (match (eval t1 ((x, v2)::tau)) with
       | InV(2, 0, w) -> w
       | InV(2, 1, w) -> appV v1 (InV(2, 1, w))
       | _ -> failwith "Internal: Wrong application of loop.")
    | SuccV(a) -> (match succmin a v2 with
                   | Min(_) -> v2
                   | Succ(v2') -> v2')
    | NatPredV -> 
        begin
          match v2 with
            | NatV(n) -> if n > 0 then NatV(n-1) else NatV(n)
            | _ -> failwith "Internal: wrong application of pred"
        end
    | ConsV(None, None) -> ConsV(Some v2, None)
    | ConsV(Some v3, None) -> ConsV(Some v3, Some v2)
    | MatchV -> 
        begin
          match v2 with
            | NilV -> InV(2, 0, UnitV)
            | ConsV(Some v3, Some v4) -> InV(2, 1, PairV(v3, v4))
            | _ -> failwith "Internal: wrong application of match"
        end
    | EqV(a, None) -> EqV(a, Some v2)
    | EqV(a, Some v3) -> if eq a v2 v3 then InV(2, 0, UnitV) else InV(2, 1, UnitV)
    | _ -> failwith "Internal: Cannot apply non-functional value."

exception FunctionalValue

let eval_closed (t: Term.t) : Term.t option =
  let rec cv2termW (v: value) =
    match v with 
      | UnitV -> mkUnitW 
      | NilV -> mkConstW None Cnil
      | ConsV(Some v1, Some v2) -> 
          mkAppW (mkAppW (mkConstW None Ccons) (cv2termW v1)) (cv2termW v2)
      | InV(n, i, v1) -> mkInW n i (cv2termW v1)
      | PairV(v1, v2) -> mkPairW (cv2termW v1) (cv2termW v2)
      | _ -> raise FunctionalValue in    
  let v = eval t [] in
    try 
      Some (cv2termW v)
    with 
      | FunctionalValue -> None
