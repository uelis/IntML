(** Term representation *)

(*  I've read the implementation of John Harrion's HOL light
 *  and the sources of the OCaml compiler when writing this file. *)

type var = string

let unusable_var = "unusable"

module Location = struct
  type pos = { column: int; line: int} 
  type loc = {start_pos: pos; end_pos: pos} 
  type t = loc option
  let none = None
end

type term_const =
  | Cprint of string
  | Cmin
  | Cbot
  | Cintconst of int
  | Cintadd
  | Cintsub
  | Cintmul
  | Cintdiv
  | Cinteq
  | Cintprint

type t =
    { desc: t_desc;      
      loc: Location.t }
and t_desc =
  | Var of var
  | ConstW of (Type.t option) * term_const 
  | UnitW 
  | PairW of t * t
  | LetW of t * (var * var * t)        (* s, <x,y>t *)
  | InW of int * int * t               (* in_n(k,t) *)
  | CaseW of t * ((var * t) list)      (* s, <x>t1, <y>t2 *)
  | AppW of t * t                      (* s, t *)
  | LambdaW of (var * (Type.t option)) * t 
  | FoldW of (Type.t * Type.t) * t
  | UnfoldW of (Type.t * Type.t) * t
  | TrW of t                           (* t *)
  | LetBoxW of t * (var * t)             (* s, <x>t *)
  | PairU of t * t                     (* s, t *)
  | LetU of t * (var * var * t)        (* s, <x,y>t *)
  | AppU of t * t                      (* s, t *)
  | LambdaU of (var * (Type.t option)) * t     
  | BoxTermU of t                      (* s *)
  | LetBoxU of t * (var * t)           (* s, <x>t *)
  | CaseU of t * (var * t) * (var * t) (* s, <x>t1, <y>t2 *)
  | CopyU of t * (var * var * t)       (* s, <x,y>t *)
  | HackU of (Type.t option) * t       (* s, t *)
  | TypeAnnot of t * (Type.t option)
                   
let mkVar x = { desc = Var(x); loc = None }
let mkConstW ty n = { desc = ConstW(ty, n); loc = None }
let mkUnitW = { desc = UnitW; loc = None}
let mkPairW s t= { desc = PairW(s, t); loc = None }
let mkLetW s ((x, y), t) = { desc = LetW(s, (x, y, t)); loc = None }
let mkInW n k t = { desc = InW(n, k, t); loc = None }
let mkInlW t = { desc = InW(2, 0, t); loc = None }
let mkInrW t = { desc = InW(2, 1, t); loc = None }
let mkCaseW s l = { desc = CaseW(s, l); loc = None }
let mkAppW s t = { desc = AppW(s, t); loc = None }
let mkLambdaW ((x, ty), t) = { desc = LambdaW((x, ty), t); loc = None }
let mkTrW t = { desc = TrW(t); loc = None }
let mkFoldW (alpha, a) s = { desc = FoldW((alpha, a), s); loc = None }
let mkUnfoldW (alpha, a) s = { desc = UnfoldW((alpha, a), s); loc = None }
let mkPairU s t= { desc = PairU(s, t); loc = None }
let mkLetU s ((x, y), t) = { desc = LetU(s, (x, y, t)); loc = None }
let mkAppU s t = { desc = AppU(s, t); loc = None }
let mkLambdaU ((x, ty), t) = { desc = LambdaU((x, ty), t); loc = None }
let mkBoxTermU s = { desc = BoxTermU(s); loc = None }
let mkLetBoxU s (x, t) = { desc = LetBoxU(s, (x, t)); loc = None }
let mkCaseU s (x1, t1) (x2, t2) = { desc = CaseU(s, (x1, t1), (x2, t2)); loc = None }
let mkCopyU s ((x, y), t) = { desc = CopyU(s, (x, y, t)); loc = None }
let mkHackU ty t = { desc = HackU(ty, t); loc = None }
let mkTypeAnnot t a = { desc = TypeAnnot(t, a); loc = None }

let rec mkLambdaWList (xs, t) = 
  match xs with 
    | [] -> t
    | x::rest -> mkLambdaW ((x, None), mkLambdaWList (rest, t))

let rec mkAppWList t args = 
  match args with 
    | [] -> t
    | x::rest -> mkAppWList (mkAppW t x) rest 

let rec free_vars (term: t) : var list =
  let abs x l = List.filter (fun z -> z <> x) l in
  match term.desc with
    | Var(v) -> [v]
    | ConstW(_, _) | UnitW -> []
    | InW(_,_,s) | FoldW(_, s) | UnfoldW(_, s) | TrW(s) 
    | BoxTermU(s) | HackU(_, s) -> free_vars s
    | PairW(s, t) | PairU (s, t) | AppW (s, t) | AppU(s, t) -> 
        (free_vars s) @ (free_vars t)
    | LetW(s, (x, y, t)) | LetU(s, (x, y, t)) | CopyU(s, (x, y, t)) ->
        (free_vars s) @ (abs x (abs y (free_vars t)))
    | LambdaW((x, _), t) | LambdaU((x, _), t) ->
        abs x (free_vars t) 
    | LetBoxW(s, (x, t)) | LetBoxU(s, (x, t)) ->
        (free_vars s) @ (abs x (free_vars t))
    | CaseW(s, l) ->
        (free_vars s) @ (List.fold_right (fun (x, t) fv -> (abs x (free_vars t)) @ fv) l [])
    | CaseU(s, (x, t), (y, u)) ->
        (free_vars s) @ (abs x (free_vars t)) @ (abs y (free_vars u))
    | TypeAnnot(t, ty) ->
        free_vars t

let rename_vars (f: var -> var) (term: t) : t =
  let rec rn term = 
    match term.desc with
    | Var(x) -> { term with desc = Var(f x) }
    | ConstW(_, _) | UnitW -> term
    | InW(n, k, s) -> { term with desc = InW(n, k, rn s) }
    | TrW(s) -> { term with desc = TrW(rn s) }
    | FoldW(ty, s) -> { term with desc = FoldW(ty, rn s) }
    | UnfoldW(ty, s) -> { term with desc = UnfoldW(ty, rn s) }
    | BoxTermU(s) -> { term with desc = BoxTermU(rn s) }
    | HackU(ty, s) -> { term with desc = HackU(ty, rn s) }
    | PairW(s, t) -> { term with desc = PairW(rn s, rn t) }
    | PairU(s, t) -> { term with desc = PairU(rn s, rn t) }
    | AppW(s, t) -> { term with desc = AppW(rn s, rn t) }
    | AppU(s, t) -> { term with desc = AppU(rn s, rn t) } 
    | LetW(s, (x, y, t)) -> { term with desc = LetW(rn s, (f x, f y, rn t)) } 
    | LetU(s, (x, y, t))  -> { term with desc = LetU(rn s, (f x, f y, rn t)) } 
    | CopyU(s, (x, y, t)) -> { term with desc = CopyU(rn s, (f x, f y, rn t)) } 
    | LambdaW((x, ty), t) -> { term with desc = LambdaW((f x, ty), rn t) } 
    | LambdaU((x, ty), t) -> { term with desc = LambdaU((f x, ty), rn t) } 
    | LetBoxW(s, (x, t)) -> { term with desc = LetBoxW(rn s, (f x, rn t)) }
    | LetBoxU(s, (x, t)) -> { term with desc = LetBoxU(rn s, (f x, rn t)) }
    | CaseW(s, l) -> 
        { term with desc = CaseW(rn s, List.map (fun (x, t) -> (f x, rn t)) l) } 
    | CaseU(s, (x, t), (y, u)) ->
        { term with desc = CaseU(rn s, (f x, rn t), (f y, rn u)) } 
    | TypeAnnot(t, ty) -> { term with desc = TypeAnnot(rn t, ty) }
  in rn term
       
let variant_var x = x ^ "'"       
let variant = rename_vars variant_var

let rec variant_var_avoid x avoid =
  let vx = variant_var x in
    if List.mem vx avoid then
      variant_var_avoid vx (x :: avoid)
    else 
      vx

(* Renames all variables with new names drawn from 
 * the given name-supply. *)
let variant_with_name_supply (fresh_var: unit -> var) (t: t) : t =
  let vars = free_vars t in
  let ren_map = List.map (fun v -> (v, fresh_var ())) vars in
    rename_vars (fun v -> List.assoc v ren_map) t 

let map_type_annots (f: Type.t option -> Type.t option) (term: t) : t = 
  let rec mta term = 
    match term.desc with
    | Var(_) | UnitW -> term 
    | ConstW(ty, s) -> { term with desc = ConstW(f ty, s) }
    | InW(n, k, s) -> { term with desc = InW(n, k, mta s) }
    | TrW(s) -> { term with desc = TrW(mta s) }
    | FoldW(ty, s) -> { term with desc = FoldW(ty, mta s) }
    | UnfoldW(ty, s) -> { term with desc = UnfoldW(ty, mta s) }
    | BoxTermU(s) -> { term with desc = BoxTermU(mta s) }
    | HackU(ty, s) -> { term with desc = HackU(f ty, mta s) }
    | PairW(s, t) -> { term with desc = PairW(mta s, mta t) }
    | PairU (s, t) -> { term with desc = PairU(mta s, mta t) }
    | AppW (s, t) -> { term with desc = AppW(mta s, mta t) }
    | AppU(s, t) -> { term with desc = AppU(mta s, mta t) } 
    | LetW(s, (x, y, t)) -> { term with desc = LetW(mta s, (x, y, mta t)) } 
    | LetU(s, (x, y, t))  -> { term with desc = LetU(mta s, (x, y, mta t)) } 
    | CopyU(s, (x, y, t)) -> { term with desc = CopyU(mta s, (x, y, mta t)) } 
    | LambdaW((x, ty), t) -> { term with desc = LambdaW((x, f ty), mta t) }
    | LambdaU((x, ty), t) -> { term with desc = LambdaU((x, f ty), mta t) } 
    | LetBoxW(s, (x, t)) -> { term with desc = LetBoxW(mta s, (x, mta t)) }
    | LetBoxU(s, (x, t)) -> { term with desc = LetBoxU(mta s, (x, mta t)) }
    | CaseW(s, l) -> 
        { term with desc = CaseW(mta s, List.map (fun (x, t) -> (x, mta t)) l) } 
    | CaseU(s, (x, t), (y, u)) ->
        { term with desc = CaseU(mta s, (x, mta t), (y, mta u)) } 
    | TypeAnnot(t, ty) -> { term with desc = TypeAnnot(mta t, f ty) }
  in mta term

let fresh_vars_for_missing_annots (term: t) : t =
  map_type_annots (function 
                     | None -> Some(Type.newty Type.Var)
                     | c -> c) term

(* substitues s for the head occurrence of x.
 * return None if t does not contain x.
 *)
let head_subst (s: t) (x: var) (t: t) : t option =
  (* Below sigma is always a permutation that maps bound 
   * variables of t to suitably fresh variables. *)
  let fvs = free_vars s in
  let apply sigma y = try List.assoc y sigma with Not_found -> y in
  let substituted = ref false in
  let rec sub sigma term =
    match term.desc with
      | Var(y) -> 
          if x = y && (not !substituted) then 
            (substituted := true; s) (* substitute only once *)
          else 
            { term with desc = Var(apply sigma y) } 
      | UnitW | ConstW(_, _) -> term
      | InW(n, k, s) -> { term with desc = InW(n, k, sub sigma s) }
      | TrW(s) -> { term with desc = TrW(sub sigma s) }
      | FoldW(ty, s) -> { term with desc = FoldW(ty, sub sigma s) }
      | UnfoldW(ty, s) -> { term with desc = UnfoldW(ty, sub sigma s) }
      | BoxTermU(s) -> { term with desc = BoxTermU(sub sigma s) }
      | HackU(ty, s) -> { term with desc = HackU(ty, sub sigma s) }
      | PairW(s, t) -> { term with desc = PairW(sub sigma s, sub sigma t) }
      | PairU (s, t) -> { term with desc = PairU(sub sigma s, sub sigma t) }
      | AppW (s, t) -> { term with desc = AppW(sub sigma s, sub sigma t) }
      | AppU(s, t) -> { term with desc = AppU(sub sigma s, sub sigma t) } 
      | LetW(s, (x, y, t)) -> { term with desc = LetW(sub sigma s, abs2 sigma (x, y, t)) } 
      | LetU(s, (x, y, t))  -> { term with desc = LetU(sub sigma s, abs2 sigma (x, y, t)) } 
      | CopyU(s, (x, y, t)) -> { term with desc = CopyU(sub sigma s, abs2 sigma (x, y, t)) } 
      | LambdaW((x, ty), t) -> 
          let (x', t') = abs sigma (x, t) in
          { term with desc = LambdaW((x', ty), t') } 
      | LambdaU((x, ty), t) -> 
          let (x', t') = abs sigma (x, t) in
          { term with desc = LambdaU((x', ty), t') } 
      | LetBoxW(s, (x, t)) -> { term with desc = LetBoxW(sub sigma s, abs sigma (x, t)) }
      | LetBoxU(s, (x, t)) -> { term with desc = LetBoxU(sub sigma s, abs sigma (x, t)) }
      | CaseW(s, l) -> 
          { term with desc = CaseW(sub sigma s, List.map (fun (x, t) -> abs sigma (x, t)) l) } 
      | CaseU(s, (x, t), (y, u)) ->
          { term with desc = CaseU(sub sigma s, abs sigma (x, t), abs sigma (y, u)) } 
      | TypeAnnot(t, ty) ->
          { term with desc = TypeAnnot(sub sigma t, ty) } 
  and abs sigma (y, u) = 
    match abs_list sigma ([y], u) with
    | [y'], u -> y', u 
    | _ -> assert false 
  and abs2 sigma (y, z, u) = 
    match abs_list sigma ([y; z], u) with
    | [y'; z'], u -> y', z', u 
    | _ -> assert false
  and abs_list sigma (l, t1) =
    if List.mem x l then (l, t1)
    else if List.for_all (fun y -> not (List.mem y fvs)) l then (* no capture *)
      (l, sub sigma t1) 
    else
        (* if substitution actually happened, i.e. Not_found is not raised,
         * then capture would occur, so we must rename *)
        let avoid = fvs @ (List.map (apply sigma) (free_vars t1)) in
        let l' = List.map (fun y -> variant_var_avoid y avoid) l in
          (l', sub ((List.combine l l') @ sigma) t1) 
  in 
  let result = sub [] t in
    if (!substituted) then Some result else None

let subst (s: t) (x: var) (t: t) : t =
  let rec sub t = 
    match head_subst s x t with
      | None -> t
      | Some t' -> sub t'
  in
    sub t

let freshen_type_vars t =
  let new_type_vars = Type.Typetbl.create 10 in
  let fv x = 
    try 
      Type.Typetbl.find new_type_vars (Type.find x)
    with Not_found ->
      let y = Type.newty Type.Var in
        Type.Typetbl.add new_type_vars (Type.find x) y;
        y in
  let f = function 
    | None -> None
    | Some a -> Some (Type.subst fv a) in
  let rec mta term = 
    match term.desc with
    | Var(_) | UnitW -> term 
    | ConstW(ty, s) -> { term with desc = ConstW(f ty, s) }
    | InW(n, k, s) -> { term with desc = InW(n, k, mta s) }
    | TrW(s) -> { term with desc = TrW(mta s) }
    | FoldW((alpha, a), s) -> 
        { term with desc = FoldW((fv alpha, Type.subst fv a), mta s) }
    | UnfoldW((alpha, a), s) -> 
        { term with desc = UnfoldW((fv alpha, Type.subst fv a), mta s) }
    | BoxTermU(s) -> { term with desc = BoxTermU(mta s) }
    | HackU(ty, s) -> { term with desc = HackU(f ty, mta s) }
    | PairW(s, t) -> { term with desc = PairW(mta s, mta t) }
    | PairU (s, t) -> { term with desc = PairU(mta s, mta t) }
    | AppW (s, t) -> { term with desc = AppW(mta s, mta t) }
    | AppU(s, t) -> { term with desc = AppU(mta s, mta t) } 
    | LetW(s, (x, y, t)) -> { term with desc = LetW(mta s, (x, y, mta t)) } 
    | LetU(s, (x, y, t))  -> { term with desc = LetU(mta s, (x, y, mta t)) } 
    | CopyU(s, (x, y, t)) -> { term with desc = CopyU(mta s, (x, y, mta t)) } 
    | LambdaW((x, ty), t) -> { term with desc = LambdaW((x, f ty), mta t) }
    | LambdaU((x, ty), t) -> { term with desc = LambdaU((x, f ty), mta t) } 
    | LetBoxW(s, (x, t)) -> { term with desc = LetBoxW(mta s, (x, mta t)) }
    | LetBoxU(s, (x, t)) -> { term with desc = LetBoxU(mta s, (x, mta t)) }
    | CaseW(s, l) -> 
        { term with desc = CaseW(mta s, List.map (fun (x, t) -> (x, mta t)) l) } 
    | CaseU(s, (x, t), (y, u)) ->
        { term with desc = CaseU(mta s, (x, mta t), (y, mta u)) } 
    | TypeAnnot(t, ty) -> { term with desc = TypeAnnot(mta t, f ty) }
  in mta t

