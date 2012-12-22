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
  | DataW of string * t list
  | FunW of t * t
  | ContW of t
  | BoxU of t * t
  | TensorU of t * t
  | FunU of t * t * t

module Data: 
sig
  type id = string
  val sumid : int -> id
  val boolid : id

  val params : id -> int
  val constructor_count : id -> int 
  val constructor_names : id -> string list 
  val constructor_types : id -> t list -> t list
  val is_recursive : id -> bool
  val is_mutable : id -> bool 

  val find_constructor: string -> id * int

  val make : id -> int -> unit
  val make_mutable : id -> unit
  val add_constructor : id -> string -> t list -> t -> unit
end

val newty : desc -> t
val next_mark : unit -> int                      

val find : t -> t
val finddesc : t -> desc
val union : t -> t -> unit

val equals : t -> t -> bool

val free_vars: t -> t list                         
val subst: (t -> t) -> t -> t
val freshen: t -> t
val freshen_list: t list -> t list
val freshen_index_types: t -> t

val unTensorW : t -> t * t                                

(* Given upper class type X, returns the pair (X^-, X^+). *)
val question_answer_pair: t -> t * t

(* Hashtbl mapping types with physical identity. *)
module Typetbl : Hashtbl.S with type key = t
