type query = 
  | Dir of string
  | DirTerm of string * Term.t
  | DirDecl of string * Decls.decl
  | DirTerm2 of string * Term.t * Term.t
  | DirType of string * Type.t
  | DirInt of string * int

val term_loc : Term.t option -> string                         
val error_msg : string -> string -> string
val print_error : string -> string -> unit
val new_decl : Decls.typed_decls -> Decls.decl -> Decls.typed_decls                         
val exec_query: Decls.typed_decls -> query -> Decls.typed_decls 
