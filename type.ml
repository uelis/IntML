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
  | DataW of string * t list
  | FunW of t * t
  | ContW of t
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
    | ContW(b1) -> free_vars b1
    | FunU(a1, b1, b2) -> 
        free_vars a1 @ (free_vars b1) @ (free_vars b2)
    | DataW(_, bs) -> List.concat (List.map free_vars bs)
    | Link _ -> assert false

let rec subst (f: t -> t) (b: t) : t =
  match (find b).desc with
    | Var -> f (find b)
    | NatW -> newty NatW
    | ZeroW -> newty ZeroW
    | OneW -> newty OneW 
    | TensorW(b1, b2) -> newty(TensorW(subst f b1, subst f b2))
    | DataW(id, bs) -> newty(DataW(id, List.map (subst f) bs))
    | FunW(b1, b2) -> newty(FunW(subst f b1, subst f b2))
    | ContW(b1) -> newty(ContW(subst f b1))
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
        | ContW(u1), ContW(v1) -> 
            equals u1 v1
        | FunU(u1, u2, u3), FunU(v1, v2, v3) ->
            (equals u1 v1) && (equals u2 v2) && (equals u3 v3)
        | DataW(idu, lu), DataW(idv, lv) ->     
            (idu = idv) &&
            (List.fold_right 
              (fun (u1, v1) e -> e && (equals u1 v1)) 
              (List.combine lu lv) true)
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

let freshen_list ts = 
  let vm = Typetbl.create 10 in
  let fv x = 
    try 
      Typetbl.find vm (find x)
    with Not_found ->
      let y = newty Var in
        Typetbl.add vm (find x) y;
        y
  in
    List.map (subst fv) ts

let freshen t = 
  match freshen_list [t] with
    | [f] -> f
    | _ -> assert false

let rec freshen_index_types (a: t) : t =
    match (find a).desc with
      | Var | ZeroW | OneW | NatW -> a
      | TensorW(b1, b2) -> newty(TensorW(freshen_index_types b1, freshen_index_types b2))
      | DataW(id, bs) -> newty(DataW(id, List.map freshen_index_types bs))
      | FunW(b1, b2) -> newty(FunW(freshen_index_types b1, freshen_index_types b2))
      | ContW(b1) -> newty(ContW(freshen_index_types b1))
      | BoxU(a1, a2) -> newty(BoxU(freshen_index_types a1, freshen_index_types a2))
      | TensorU(b1, b2) -> newty(TensorU(freshen_index_types b1, freshen_index_types b2))
      | FunU(a1, b1, b2) -> newty(FunU(newty Var, freshen_index_types b1, freshen_index_types b2))
      | Link _ -> assert false

module Data =
struct
  type id = string

  type d = { name : string;
             params : t list;
             constructors : (string * t) list }

  let datatypes = Hashtbl.create 10
  let boolid = 
    Hashtbl.add datatypes "bool"
      { name = "bool"; params = []; 
        constructors = ["True", newty OneW;
                        "False", newty OneW] };
    "bool"

  let sumid =
    let sumtypes = Hashtbl.create 10 in
      fun (n : int) ->
        try Hashtbl.find sumtypes n 
        with Not_found ->
              let name = "sum" ^ (string_of_int n) in
              let l = Listutil.init n (fun i -> i, newty Var) in
              let params = List.map snd l in
              let constructors = List.map (fun (i, alpha) -> 
                                             (if n = 2 && i = 0 then "Inl" 
                                             else if n = 2 && i = 1 then "Inr" 
                                             else Printf.sprintf "In_%i_%i" n i), 
                                             alpha) l in
              let d = { name = name; params = params; constructors = constructors } in
                Hashtbl.add datatypes name d;
                Hashtbl.add sumtypes n name;
                name
                  
  (* declare nullary and binary sums by default; all others are declared on demand *)
  let _ = ignore (sumid 0); ignore (sumid 2)

  let params id = List.length (Hashtbl.find datatypes id).params
  let constructor_names id = 
    let cs = (Hashtbl.find datatypes id).constructors in
      List.map fst cs

  let constructor_types id newparams = 
    let cs = (Hashtbl.find datatypes id).constructors in
    let ts = List.map snd cs in
    let ps = (Hashtbl.find datatypes id).params in
    let param_subst alpha = 
      let l = List.combine ps newparams in
        try List.assoc alpha l with Not_found -> alpha in
      List.map (subst param_subst) ts

  let is_recursive id =
    let rec check_rec a =
      match finddesc a with
        | Var | ZeroW | OneW | NatW -> false
        | ContW(b1) -> check_rec b1
        | TensorW(b1, b2) | FunW(b1, b2) -> check_rec b1 || (check_rec b2)
        | DataW(id', bs) -> id = id' || List.exists check_rec bs
        | BoxU(_, _) | TensorU(_, _) | FunU(_, _, _) | Link _ -> assert false in 
    let freshparams = Listutil.init (params id) (fun i -> newty Var) in
    let ct = constructor_types id freshparams in
      List.exists check_rec ct

  exception Found of id * int 

  let find name =
    try
      Hashtbl.iter (fun id d -> 
                      Array.iteri (fun i (cname, _) ->
                                    if cname = name then raise (Found (id, 0)))
                        (Array.of_list d.constructors)) datatypes;
        raise Not_found
    with Found (id, i) -> id

  let find_constructor name =
    try
      Hashtbl.iter (fun id d -> 
                      Array.iteri (fun i (cname, _) ->
                                    if cname = name then raise (Found (id, i)))
                        (Array.of_list d.constructors)) datatypes;
        raise Not_found
    with Found (id, i) -> id, i

  (* muss sichergehen, dass aus parametervariablen nicht durch Unifikation
   * Typen werden *)
  let make name = 
    Hashtbl.add datatypes name { name = name; params = []; constructors = [] }

  let add_param id var = 
    let d = Hashtbl.find datatypes id in
    let d' = { d with params = d.params @ [var] } in
      Hashtbl.replace datatypes id d'

  (* TODO: check for duplicates, parameters *)
  let add_constructor id name arg =
    let d = Hashtbl.find datatypes id in
    let d' = { d with constructors = d.constructors @ [name, arg] } in
      Hashtbl.replace datatypes id d'
end

  
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
            (newty (DataW(Data.sumid 2, [bm1; bm2])), 
             newty (DataW(Data.sumid 2, [bp1; bp2])))
      | FunU(a, b1, b2) ->
          let (bm1, bp1) = qap b1 in
          let (bm2, bp2) = qap b2 in
            (newty (DataW(Data.sumid 2, [newty (TensorW(a, bp1)); bm2])), 
             newty (DataW(Data.sumid 2, [newty (TensorW(a, bm1)); bp2])))
      | _ -> failwith "error"
  in qap s

