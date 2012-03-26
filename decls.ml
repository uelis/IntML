(** Declarations used in toplevel.
*)

type decl = 
  | TermDeclW of Term.var * Term.t
  | TermDeclU of Term.var * Term.t

type decls = decl list

type typed_decl = 
  | TypedTermDeclW of Term.var * Term.t * Type.t
  | TypedTermDeclU of Term.var * Term.t * Type.t

type typed_decls = typed_decl list                                     

let subst_decl_in_term (d: decl) (s: Term.t) : Term.t =
  (* fsubst t v s substitutes t for v in s, such that each time t is 
   * pasted all the type variables in t are replaced by fresh ones *)
  let rec fsubst t v s =
    match Term.head_subst (Term.freshen_type_vars t) v s with
      | Some s' -> fsubst t v s'
      | None -> s
  in 
    match d with
      | TermDeclW(v, t) | TermDeclU(v, t) -> fsubst t v s

let subst_typed_decl_in_term = function
  | TypedTermDeclW(v, t, _) -> subst_decl_in_term (TermDeclW(v, t))
  | TypedTermDeclU(v, t, _) -> subst_decl_in_term (TermDeclU(v, t))

(* expands d in decl *)                                               
let subst_decl_in_decl (d: decl) : decl -> decl =
  function
    | TermDeclW(w, s) -> TermDeclW(w, subst_decl_in_term d s)
    | TermDeclU(w, s) -> TermDeclU(w, subst_decl_in_term d s)

let subst_typed_decl_in_decl (d: typed_decl) : decl -> decl =
  function
    | TermDeclW(w, s) -> TermDeclW(w, subst_typed_decl_in_term d s)
    | TermDeclU(w, s) -> TermDeclU(w, subst_typed_decl_in_term d s)

let rec subst_decls (ds: decls) : decls =
  match ds with 
    | [] -> []
    | d :: rest ->
        d :: subst_decls (List.map (subst_decl_in_decl d) rest)
