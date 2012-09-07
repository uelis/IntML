(** Evaluation of working class terms.
  *)
open Term

(* evaluation of closed terms *)  

type env = (var * value) list
and value =
  | NatPredV 
  | IntV of int
  | FoldV of (Type.t * Type.t) * value
  | UnitV 
  | InV of int * int * value
  | PairV of value * value
  | FunV of env * var * Term.t
  | TrV of env * var * Term.t
  | LoopV of env * var * Term.t
  | InteqV of value option
  | IntaddV of value option
  | IntsubV of value option
  | IntmulV of value option
  | IntdivV of value option
  | IntprintV

let rec min (ty: Type.t) =
  match Type.finddesc ty with
  | Type.Var -> 
      Printf.printf "warning: trying to evaluate polymophic min; instantiating variables with 1\n";
      UnitV  
  | Type.NatW -> IntV(0)
  | Type.OneW -> UnitV
  | Type.TensorW(a, b) -> PairV(min a, min b)
  | Type.SumW(a :: l) -> InV(1 + (List.length l), 0, min a)
  | Type.ZeroW | Type.SumW [] | Type.FunU(_, _, _) | Type.TensorU (_, _)
  | Type.BoxU(_,_) | Type.FunW (_, _) | Type.Link _ | Type.MuW _ ->
      failwith "internal: min" 

type succOrMin =
  | Succ of value
  | Min of value

let rec succmin (ty: Type.t) (v: value) : succOrMin =
  match Type.finddesc ty, v with
  | Type.Var, _ -> 
      Printf.printf "warning: trying to evaluate polymophic succ; instantiating variables with 1\n";
      Min(UnitV)  
  | Type.NatW, IntV(n) -> Succ(IntV(n+1))
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
  | Type.NatW, IntV(v), IntV(w) -> v=w
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
    | ConstW(Some a, Cmin) -> min a
    | ConstW(_, Cintconst(i)) -> IntV(i)
    | ConstW(_, Cintprint) -> IntprintV
    | ConstW(_, Cinteq) -> InteqV(None)
    | ConstW(_, Cintadd) -> IntaddV(None)
    | ConstW(_, Cintsub) -> IntsubV(None)
    | ConstW(_, Cintmul) -> IntmulV(None)
    | ConstW(_, Cintdiv) -> IntdivV(None)
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
    | FoldW((alpha, a), t) ->
        let v = eval t sigma in
          FoldV((alpha, a), v)
    | UnfoldW(_, t) ->
        (match eval t sigma with
           | FoldV(_, v) -> v
           | _ -> failwith "Internal: unfold applied to non-fold value."
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
    | NatPredV -> 
        begin
          match v2 with
            | IntV(n) -> if n > 0 then IntV(n-1) else IntV(n)
            | _ -> failwith "Internal: wrong application of pred"
        end
    | InteqV(None) -> InteqV(Some v2)
    | InteqV(Some v3) -> 
        (match v2, v3 with
           | IntV(v2'), IntV(v3') -> 
               if v2' = v3' then InV(2, 0, UnitV) else InV(2, 1, UnitV)
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
      | IntV(i) -> mkConstW None (Cintconst(i))
      | InV(n, i, v1) -> mkInW n i (cv2termW v1)
      | PairV(v1, v2) -> mkPairW (cv2termW v1) (cv2termW v2)
      | FoldV((alpha, a), v) -> mkFoldW (alpha, a) (cv2termW v)
      | _ -> raise FunctionalValue in    
  let v = eval t [] in
    try 
      Some (cv2termW v)
    with 
      | FunctionalValue -> None
