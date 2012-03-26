
module type S = sig

  type tag
  type typeEq = Type.t * Type.t * (tag option)

  type failure_reason =
    | Equation_failed of typeEq
    | Cyclic_type of typeEq 

  exception Not_Unifiable of failure_reason

  val unify_pairs: typeEq list -> unit

  val unify: Type.t -> Type.t -> unit

end

module Unify(Tag : sig type t end) : S 
               with type tag = Tag.t                                     
