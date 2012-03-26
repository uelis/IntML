type t = 
    { mutable desc : desc; 
      mutable mark : int;
      mutable id : int
    }

and desc = 
  | Link of t
  | Var
  | ZeroW
  | OneW
  | TensorW of t * t
  | SumW of t list
  | FunW of t * t
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

let rec equals (u: t) (v: t) : bool =
  let ur = find u in
  let vr = find v in
    if ur == vr then true
    else 
      match ur.desc, vr.desc with
        | Var, Var -> 
            false
        | ZeroW, ZeroW | OneW, OneW -> 
            true
        | TensorW(u1, u2), TensorW(v1, v2) | TensorU(u1, u2), TensorU(v1, v2) 
        | FunW(u1, u2), FunW(v1, v2) | BoxU(u1, u2), BoxU(v1, v2) ->
            (equals u1 v1) && (equals u2 v2)
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

let rec rename (f: t -> t) : t -> t =
  let rec ren (b: t) : t = 
    match (find b).desc with
      | Var -> f (find b)
      | ZeroW -> newty ZeroW
      | OneW -> newty OneW 
      | TensorW(b1, b2) -> newty(TensorW(ren b1, ren b2))
      | SumW(bs) -> newty(SumW(List.map ren bs))
      | FunW(b1, b2) -> newty(FunW(ren b1, ren b2))
      | BoxU(a1, a2) -> newty(BoxU(ren a1, ren a2))
      | TensorU(b1, b2) -> newty(TensorU(ren b1, ren b2))
      | FunU(a1, b1, b2) -> newty(FunU(ren a1, ren b1, ren b2))
      | Link _ -> assert false
  in ren

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
    rename fv t

let rec freshen_index_types (a: t) : t =
    match (find a).desc with
      | Var | ZeroW | OneW -> a
      | TensorW(b1, b2) -> newty(TensorW(freshen_index_types b1, freshen_index_types b2))
      | SumW(bs) -> newty(SumW(List.map freshen_index_types bs))
      | FunW(b1, b2) -> newty(FunW(freshen_index_types b1, freshen_index_types b2))
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
