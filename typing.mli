type contextW = (Term.var * Type.t) list 
type contextU = (Term.var * (Type.t * Type.t)) list 

exception Typing_error of Term.t option * string                  

type type_constraint
val eq_constraint: Type.t -> Type.t -> type_constraint
val leq_constraint: Type.t -> Type.t -> type_constraint
val string_of_constraint: type_constraint -> string

val solve_constraints: type_constraint list -> unit

exception Not_Leq
val embed : Type.t -> Type.t -> Term.t
val project : Type.t -> Type.t -> Term.t

(* Principal types. *)

(* raises Typing_error, unifies types as a side effect *)
val principal_typeW: contextW -> Term.t -> Type.t 

(* raises Typing_error, unifies types as a side effect *)
val principal_typeU: contextW -> contextU -> Term.t -> Type.t
