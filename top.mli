val term_loc : Term.t option -> string                         
val error_msg : string -> string -> string
val print_error : string -> string -> unit
val new_decl : Decls.typed_decls -> Decls.decl -> Decls.typed_decls                         
val exec_query: Decls.typed_decls -> Query.query -> Decls.typed_decls 
