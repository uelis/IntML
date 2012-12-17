
type query = 
  | Dir of string
  | DirTerm of string * Term.t
  | DirData of Type.Data.id
  | DirDecl of string * Decls.decl
  | DirTerm2 of string * Term.t * Term.t
  | DirType of string * Type.t
  | DirInt of string * int

