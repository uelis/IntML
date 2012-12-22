val termW_of_circuit: Circuit.circuit -> Term.t * Type.t

val in_k : int -> int -> Term.t -> Term.t
val out_k : Term.t -> int -> int * Term.t
val message_passing_term: Circuit.circuit -> Term.t
