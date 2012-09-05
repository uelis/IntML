type t = 
    { mutable desc : desc; 
      mutable mark : int;
      mutable id : int
    }

and desc = 
  | Link of t
  | Var
  | NatW
  | ZeroW
  | OneW
  | TensorW of t * t
  | SumW of t list
  | FunW of t * t
  | MuW of t * t
  | BoxU of t * t
  | TensorU of t * t
  | FunU of t * t * t                          

let next_id = ref 0                      
let newty d = 
  incr next_id; { desc = d; mark = 0; id = !next_id }

let current_mark : int ref = ref 0 
let next_mark () : int = incr current_mark; !current_mark                     

let rec find (t : t) : t =
    match t.desc with
    | Link l -> 
        let r = find l 
        in t.desc <- Link r; 
           r
    | _ -> t

let finddesc (t : t) = (find t).desc

let union (t1 : t) (t2 : t) : unit =
  (find t1).desc <- Link (find t2)

type type_t = t                

let rec free_vars (b: t) : t list =
  match (find b).desc with
    | Var -> [find b]
    | NatW | ZeroW | OneW -> []
    | TensorW(b1, b2) | FunW(b1, b2) | TensorU(b1, b2) | BoxU(b1, b2) ->
        free_vars b1 @ (free_vars b2)
    | FunU(a1, b1, b2) -> 
        free_vars a1 @ (free_vars b1) @ (free_vars b2)
    | SumW(bs) -> List.concat (List.map free_vars bs)
    | MuW(alpha, a) -> 
        let fva = free_vars a in
          List.filter (fun beta -> not (find beta == find alpha)) fva
    | Link _ -> assert false

let rec subst (f: t -> t) (b: t) : t =
  match (find b).desc with
    | Var -> f (find b)
    | NatW -> newty NatW
    | ZeroW -> newty ZeroW
    | OneW -> newty OneW 
    | TensorW(b1, b2) -> newty(TensorW(subst f b1, subst f b2))
    | SumW(bs) -> newty(SumW(List.map (subst f) bs))
    | FunW(b1, b2) -> newty(FunW(subst f b1, subst f b2))
    | MuW(alpha, a) -> 
        let beta = newty Var in
        let a' = subst (fun x -> if x = alpha then beta else x) a in 
        newty(MuW(alpha, subst f a'))
    | BoxU(a1, a2) -> newty(BoxU(subst f a1, subst f a2))
    | TensorU(b1, b2) -> newty(TensorU(subst f b1, subst f b2))
    | FunU(a1, b1, b2) -> newty(FunU(subst f a1, subst f b1, subst f b2))
    | Link _ -> assert false

let rec equals (u: t) (v: t) : bool =
  let ur = find u in
  let vr = find v in
    if ur == vr then true
    else 
      match ur.desc, vr.desc with
        | Var, Var -> 
            false
        | NatW, NatW | ZeroW, ZeroW | OneW, OneW -> 
            true
        | TensorW(u1, u2), TensorW(v1, v2) | TensorU(u1, u2), TensorU(v1, v2) 
        | FunW(u1, u2), FunW(v1, v2) | BoxU(u1, u2), BoxU(v1, v2) ->
            (equals u1 v1) && (equals u2 v2)
        | MuW(alpha, a), MuW(beta, b) ->
            (* TODO: inefficient *)
            let gamma = newty Var in
            (equals 
               (subst (fun x -> if x == alpha then gamma else x) a) 
               (subst (fun x -> if x == beta then gamma else x) b) )
        | FunU(u1, u2, u3), FunU(v1, v2, v3) ->
            (equals u1 v1) && (equals u2 v2) && (equals u3 v3)
        | SumW(lu), SumW(lv) ->            
            List.fold_right 
              (fun (u1, v1) e -> e && (equals u1 v1)) 
              (List.combine lu lv) true
        | Link _, _ | _, Link _ -> assert false
        | _, _ -> 
            false

module Typetbl = Hashtbl.Make(
struct
  type t = type_t
  let equal s t = (s == t)
  let hash s = s.id
end
)

let freshen t = 
  let vm = Typetbl.create 10 in
  let fv x = 
    try 
      Typetbl.find vm (find x)
    with Not_found ->
      let y = newty Var in
        Typetbl.add vm (find x) y;
        y
  in
    subst fv t

let rec freshen_index_types (a: t) : t =
    match (find a).desc with
      | Var | ZeroW | OneW | NatW -> a
      | TensorW(b1, b2) -> newty(TensorW(freshen_index_types b1, freshen_index_types b2))
      | SumW(bs) -> newty(SumW(List.map freshen_index_types bs))
      | FunW(b1, b2) -> newty(FunW(freshen_index_types b1, freshen_index_types b2))
      | MuW(alpha, a) -> newty(MuW(alpha, freshen_index_types a))
      | BoxU(a1, a2) -> newty(BoxU(freshen_index_types a1, freshen_index_types a2))
      | TensorU(b1, b2) -> newty(TensorU(freshen_index_types b1, freshen_index_types b2))
      | FunU(a1, b1, b2) -> newty(FunU(newty Var, freshen_index_types b1, freshen_index_types b2))
      | Link _ -> assert false
  
let question_answer_pair s : t * t =
  let vm = Typetbl.create 10 in
  let rec qap t =
    match (find t).desc with
      | Var -> 
          begin
            try 
              Typetbl.find vm (find t)
            with Not_found ->
              let betam = newty Var in
              let betap = newty Var in
                Typetbl.replace vm (find t) (betam, betap);
                (betam, betap)
          end
      | BoxU(a1, a2) -> (a1, a2)
      | TensorU(b1, b2) ->
          let (bm1, bp1) = qap b1 in
          let (bm2, bp2) = qap b2 in
            (newty (SumW[bm1; bm2]), newty (SumW[bp1; bp2]))
      | FunU(a, b1, b2) ->
          let (bm1, bp1) = qap b1 in
          let (bm2, bp2) = qap b2 in
            (newty (SumW[newty (TensorW(a, bp1)); bm2]), 
             newty (SumW[newty (TensorW(a, bm1)); bp2]))
      | _ -> failwith "error"
  in qap s
