(** Evaluation of working class terms.
  *)
open Term

(* evaluation of closed terms *)  

type basevalue =   
  | BIntV of int
  | BFoldV of basevalue
  | BUnitV 
  | BInV of int * int * basevalue
  | BPairV of basevalue * basevalue

module Valtbl = Hashtbl.Make (
struct
  type t = basevalue
  let rec equal v1 v2= 
    match v1, v2 with
    | BUnitV, BUnitV -> true
    | BIntV(v), BIntV(w) -> v=w
    | BFoldV(v), BFoldV(w) -> v=w
    | BPairV(v11, v12), BPairV(v21, v22) -> equal v11 v21 && equal v12 v22
    | BInV(m, i, v1'), BInV(n, j, v2') -> 
        (m = n) && (i = j) && (equal v1' v2')
    | _ -> false
  let hash = Hashtbl.hash
end
)

type env = (var * value) list
and value =
  | NatPredV 
  | IntV of int
  | FoldV of (Type.t * Type.t) * value
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
  | HashputV of value option * value option
  | HashgetV of value option
  | IntprintV

let rec basevalue_of_value v =
  match v with
    | IntV(i) -> BIntV(i)
    | FoldV(_, t) -> BFoldV(basevalue_of_value t)
    | UnitV -> BUnitV
    | InV(n, i, t) -> BInV(n, i, basevalue_of_value t)
    | PairV(s, t) -> BPairV(basevalue_of_value s, basevalue_of_value t)
    | _ -> assert false

let memtbls = Hashtbl.create 2
let memtbl i = 
  try 
    Hashtbl.find memtbls i 
  with 
    | Not_found ->
        let t = (Valtbl.create 10 : value Valtbl.t) in
          Hashtbl.replace memtbls i t;
          t

let rec cv2termW (v: value) : Term.t =
  match v with 
    | UnitV -> mkUnitW 
    | IntV(i) -> mkConstW (Cintconst(i))
    | InV(n, i, v1) -> mkInW n i (cv2termW v1)
    | PairV(v1, v2) -> mkPairW (cv2termW v1) (cv2termW v2)
    | FoldV((alpha, a), v) -> mkFoldW (alpha, a) (cv2termW v)
    | _ -> assert false

type succOrMin =
  | Succ of value
  | Min of value

(* Equality on values of basic type:
 * A ::= 1 | int | A*A | A+A | mu alpha. A(alpha)
 *)
let rec eq (ty: Type.t) (v1: value) (v2: value) : bool =
  match Type.finddesc ty, v1, v2 with
  | Type.Var, _, _ -> 
      Printf.printf "warning: trying to evaluate polymophic eq; instantiating variables with 1\n";
      true
  | Type.OneW, _, _ -> true
  | Type.NatW, IntV(v), IntV(w) -> v=w
  | Type.MuW(_), FoldV(_, v), FoldV(_, w) -> v=w
  | Type.TensorW(a, b), PairV(v11, v12), PairV(v21, v22) -> eq a v11 v21 && eq b v12 v22
  | Type.SumW(l), InV(m, i, v1'), InV(n, j, v2') -> 
         (m = n) && (i = j) && (eq (List.nth l i) v1' v2')
  | _ -> false

let newid =
  let n = ref 0 in
    fun () -> n := !n + 1; !n

let rec eval (t: Term.t) (sigma : env) : value =
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
    | ConstW(Chashnew) -> IntV(newid ())
    | ConstW(Chashfree) -> UnitV
    | ConstW(Chashput) -> HashputV(None, None)
    | ConstW(Chashget) -> HashgetV(None)
    | ConstW(Cbot) ->  failwith "nontermination!"
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
    | LambdaU (_, _)|AppU (_, _)|LetU (_, _)|PairU (_, _) | MemoU(_)
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
    | HashputV(None, None) -> HashputV(Some v2, None)
    | HashputV(Some table, None) -> HashputV(Some table, Some v2)
    | HashputV(Some table, Some key) -> 
        (match table with
           | IntV t -> 
(*               Printf.printf "put: %i\n" (Valtbl.length memtbl); *)
               Valtbl.replace (memtbl t) (basevalue_of_value key) v2; 
               UnitV 
           | _ -> assert false)
    | HashgetV(None) -> HashgetV(Some v2)
    | HashgetV(Some v3) -> 
        (match v3 with
           | IntV t -> 
(*               Printf.printf "get %s\n" (Printing.string_of_termW (cv2termW
 *               v2)); *)
               (try InV(2, 0, Valtbl.find (memtbl t) (basevalue_of_value v2)) with 
                 | Not_found -> InV(2, 1, UnitV))
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
      | FoldV((alpha, a), v) -> mkFoldW (alpha, a) (cv2termW v)
      | _ -> raise FunctionalValue in    
  let v = eval t [] in
    try 
      Some (cv2termW v)
    with 
      | FunctionalValue -> None
