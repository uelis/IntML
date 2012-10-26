type label = { 
  name: int; 
  message_type: Type.t
}
type let_bindings = (Term.t * (Term.var * Term.var)) list 
type block = 
    Unreachable of label
  | Direct of label * let_bindings * Term.t * label
  | Branch of label * let_bindings * (Term.t * (Term.var * Term.t * label) * (Term.var * Term.t * label))

val reduce: Term.t -> Term.t
val trace: Compile.circuit -> block list                                       
