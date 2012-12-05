
type query = 
  | Dir of string
  | DirTerm of string * Term.t
  | DirDecl of string * Decls.decl
  | DirTerm2 of string * Term.t * Term.t
  | DirType of string * Type.t
  | DirInt of string * int

