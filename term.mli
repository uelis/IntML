(*
 *  terms.ml
 *
 *  I've read the implementation of John Harrion's HOL ligt
 *  before writing this file.
 *
 *)

type var = string

val unusable_var : var

module Location : sig
  type pos = { column: int; line: int} 
  type loc = {start_pos: pos; end_pos: pos} 
  type t = loc option
  val none: t
end

type term_const =
  | Cprint of string
  | Cbot
  | Cintconst of int
  | Cintadd
  | Cintsub
  | Cintmul
  | Cintdiv
  | Cinteq
  | Cintslt
  | Cintprint

type t = { desc: t_desc;      
           loc: Location.t }
and t_desc =
  | Var of var
  | ConstW of term_const 
  | UnitW 
  | PairW of t * t
  | LetW of t * (var * var * t)          (* s, <x,y>t *)
  | InW of int * int * t                 (* in_n(k,t) *)
  | CaseW of t * ((var * t) list)        (* s, <x1>t1, <x2>t2, ... *)
  | AppW of t * t                        (* s, t *)
  | LambdaW of (var * Type.t option) * t (* <x>s *)
  | FoldW of (Type.t * Type.t) * t
  | UnfoldW of (Type.t * Type.t) * t
  | AssignW of (Type.t * Type.t) * t * t
  | DeleteW of (Type.t * Type.t) * t
  | LoopW of t * (var * t) 
  | LetBoxW of t * (var * t)             (* s, <x>t *)
  | MemoU of t                    
  | SuspendU of t                    
  | ForceU of t                    
  | PairU of t * t                       (* s, t *)
  | LetU of t * (var * var * t)          (* s, <x,y>t *)
  | AppU of t * t                        (* s, t *)
  | LambdaU of (var * Type.t option) * t     
  | BoxTermU of t                        (* s *)
  | LetBoxU of t * (var * t)             (* s, <x>t *)
  | CaseU of t * (var * t) * (var * t)   (* s, <x>t1, <y>t2 *)
  | CopyU of t * (var * var * t)         (* s, <x,y>t *)
  | HackU of Type.t option * t                (* s, t *)
  | TypeAnnot of t * (Type.t option)
                   
val mkVar : var -> t
val mkConstW : term_const -> t
val mkUnitW : t
val mkPairW : t -> t -> t
val mkLetW : t -> (var * var) * t -> t
val mkFstW : t -> t
val mkSndW : t -> t
val mkInW : int -> int -> t -> t
val mkInlW : t -> t
val mkInrW : t -> t
val mkCaseW : t -> (var * t) list -> t
val mkAppW : t -> t -> t
val mkLambdaW : (var * Type.t option) * t -> t
val mkTrW : t -> t
val mkLoopW : t -> (var * t) -> t
val mkFoldW : Type.t * Type.t -> t -> t
val mkUnfoldW : Type.t * Type.t -> t -> t
val mkAssignW : Type.t * Type.t -> t -> t -> t
val mkDeleteW : Type.t * Type.t -> t -> t
val mkPairU : t -> t -> t
val mkLetU : t -> (var * var) * t -> t
val mkAppU : t -> t -> t
val mkLambdaU : (var * Type.t option) * t -> t
val mkBoxTermU : t -> t
val mkLetBoxU : t -> var * t -> t
val mkCaseU : t -> var * t -> var * t -> t
val mkCopyU : t -> (var * var) * t -> t
val mkHackU : Type.t option -> t -> t
val mkTypeAnnot : t -> Type.t option -> t
val mkLambdaWList : var list * t -> t
val mkAppWList : t -> t list -> t                                  

val free_vars : t -> var list 
val rename_vars : (var -> var) -> t -> t 
val variant_var : var -> var
val variant_var_avoid: var -> var list -> var
val variant : t -> t

(* Renames all variables with new names drawn from 
 * the given name-supply. *)
val variant_with_name_supply : (unit -> var) -> t -> t 

(* val map_type_annots : (Type.t option -> Type.t option) -> t -> t *)

val fresh_vars_for_missing_annots : t -> t

(* head_subst s x t substitues s for the head occurrence of x.
 * returns None if t does not contain x. *)
val head_subst: t -> var -> t -> t option
(* TODO: (subst "<x,x>" "x" "x") should be incorrect *)
val subst: t -> var -> t -> t

val freshen_type_vars : t -> t
