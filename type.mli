(* The representation of types uses a union find data
 * structure that makes unification easy. 
 * I learned about this representation of types
 * from the following article (Section 1.4):
 *   Didier Rémy. Using, Understanding, and Unraveling
 *   The OCaml Language. LNCS 2395. Springer-Verlag 2002
 *   http://pauillac.inria.fr/~remy/cours/appsem/
 *)

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
  | HashW of t * t
  | BoxU of t * t
  | TensorU of t * t
  | FunU of t * t * t

val newty : desc -> t
val next_mark : unit -> int                      

val find : t -> t
val finddesc : t -> desc
val union : t -> t -> unit

val equals : t -> t -> bool

val free_vars: t -> t list                         
val subst: (t -> t) -> t -> t
val freshen: t -> t
val freshen_index_types: t -> t

(* Given upper class type X, returns the pair (X^-, X^+). *)
val question_answer_pair: t -> t * t

(* Hashtbl mapping types with physical identity. *)
module Typetbl : Hashtbl.S with type key = t
