type label = { 
  name: int; 
  message_type: Type.t
}

type let_bindings = (Term.t * (Term.var * Term.var)) list 

type block = 
    Unreachable of label
  | Direct of label * Term.var * let_bindings * Term.t * label
  | InDirect of label * Term.var * let_bindings * Term.t * (label list)
  | Branch of label * Term.var * let_bindings * (Type.Data.id * Term.t * (Term.var * Term.t * label) list)
  | Return of label * Term.var * let_bindings * Term.t * Type.t

type func = {
  func_name : string;
  argument_type: Type.t;
  entry_block : int;
  blocks : block list;
  return_type: Type.t;
}
                                       
val reduce: Term.t -> let_bindings * Term.t
val trace: Circuit.circuit -> func                                       
val string_of_func : func -> string
