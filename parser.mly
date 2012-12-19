%{
(************************************************************************
*
*  parser.mly
*
************************************************************************)

open Lexing
open Parsing
open Term
open Decls

let error msg =
  Printf.printf "Syntax Error: %s\n" msg;
  raise Parsing.Parse_error

let mkTerm d : Term.t =
  let s = Parsing.symbol_start_pos () in 
  let e = Parsing.symbol_end_pos () in 
  let lp pos = {
    Location.line = pos.pos_lnum; 
    Location.column = pos.pos_cnum - pos.pos_bol + 1 } in
  { Term.desc = d; loc = Some({Location.start_pos = lp s; Location.end_pos = lp e }) } 

let type_vars = Hashtbl.create 10 

let type_var (a : string) : Type.t = 
   try 
     Hashtbl.find type_vars a
   with Not_found ->
     let alpha = Type.newty Type.Var in
     Hashtbl.add type_vars a alpha;
     alpha

let clear_type_vars () = Hashtbl.clear type_vars  

%}

%token TokLBrace
%token TokRBrace
%token TokLParen
%token TokRParen
%token TokLAngle
%token TokRAngle
%token TokRightArrow
%token TokLBracket
%token TokRBracket
%token TokLambda
%token TokPlus
%token TokMinus
%token TokTimes
%token TokDiv
%token TokComma
%token TokDot
%token TokQuote
%token TokColon
%token TokColonEquals
%token TokSemicolon
%token TokSharp
%token TokKwType
%token TokKwUnit
%token TokDelete
%token TokKwNat
%token TokKwBool
%token TokEquals
%token TokKwIf
%token TokKwThen
%token TokKwElse
%token TokKwPrint
%token TokKwMin
%token TokKwSucc
%token TokKwPred
%token TokKwEq
%token TokKwHack
%token TokLoop
%token TokZero
%token TokOne
%token TokLet 
%token TokAs
%token TokKwOf 
%token TokIn 
%token TokKwCopy
%token TokCase
%token TokKwInl 
%token TokKwInr 
%token TokLetW
%token TokLetU
%token TokLolli
%token TokMulti
%token TokMemo
%token TokForce
%token TokSuspend
%token TokCont
%token TokBang
%token TokVertbar
%token <int> TokNum
%token <string> TokIdent 
%token <string> TokConstr 
%token <string> TokString 
%token TokEof

%left TokVertbar 
%left TokEquals 
%left TokLAngle
%left TokPlus TokMinus
%left TokTimes TokDiv

%start decls
%start top_query
%start termW
%type <Decls.decls> decls
%type <Query.query> top_query
%type <Term.t> termW
%type <Type.t> typeW
%type <Type.t> typeU

%%

top_query: 
    | termW TokEof
      { clear_type_vars (); Query.DirTerm("eval", $1) }
    | decl TokEof
      { Query.DirDecl("decl", $1) }
    | TokSharp TokIdent TokEof
      { Query.Dir($2) }
    | TokSharp TokIdent termU_atom TokEof
      { Query.DirTerm($2, $3) }
    | TokSharp TokIdent termU_atom termW TokEof
      { Query.DirTerm2($2, $3, $4) }
    | TokSharp TokIdent TokNum TokEof
      { Query.DirInt($2, $3) }
    | dataW
      { Query.DirData($1) }

decls:
    | TokEof
      { [] }
    | decl decls
      { $1 :: $2 }
    | dataW decls
      { $2 }

decl:
    | TokLetW identifier TokEquals termW
       { clear_type_vars (); TermDeclW($2, $4) }
    | TokLetW identifier TokColon typeW TokEquals termW
       { clear_type_vars (); TermDeclW($2, mkTerm (TypeAnnot($6, Some $4))) }
    | TokLetU identifier TokEquals termU
       { clear_type_vars (); TermDeclU($2, $4) }
    | TokLetU identifier TokColon typeU TokEquals termU
       { clear_type_vars (); TermDeclU($2, mkTerm (TypeAnnot($6, Some $4))) }

identifier:
    | TokIdent
        { $1 }

termW:    
    | TokLambda identifier TokRightArrow termW 
       { mkTerm (LambdaW(($2, None), $4)) }
    | TokLambda TokLParen identifier TokColon typeW TokRParen TokRightArrow termW 
       { mkTerm (LambdaW(($3, Some $5), $8)) }
    | TokLet TokLParen identifier TokComma identifier TokRParen TokEquals termW TokIn termW
      { mkTerm (LetW($8, ($3, $5, $10))) }
    | TokKwIf termW TokKwThen termW TokKwElse termW
      { mkTerm (CaseW(Type.Data.boolid, $2, [(unusable_var, $4); (unusable_var, $6)])) }
    | TokLet identifier TokEquals termW TokLoop termW
       { mkTerm (LoopW ($4, ($2, $6))) }
    | TokLet identifier TokEquals termW TokIn termW
       { mkTerm (AppW (mkTerm (LambdaW(($2, None), $6)), $4)) }
    | TokLet TokLBracket identifier TokRBracket TokEquals termU TokIn termW
       { mkTerm (LetBoxW($6, ($3, $8))) }
    | TokKwPrint termW
       { mkTerm (AppW(mkTerm (ConstW(Cintprint)), $2)) }
    | termW_app TokEquals termW_app
       { mkTerm (AppW(mkTerm (AppW(mkTerm (ConstW(Cinteq)), $1)), $3)) }
    | termW_app TokLAngle termW_app
       { mkTerm (AppW(mkTerm (AppW(mkTerm (ConstW(Cintslt)), $1)), $3)) }
    | termW_app TokColonEquals TokLAngle TokIdent TokRAngle  termW
       { mkTerm (AssignW($4, $1, $6)) }
    | TokDelete TokLAngle typeW TokDot typeW TokRAngle termW
       { mkTerm (DeleteW(($3, $5), $7)) }
    | TokCase termW TokKwOf termW_cases
       { let id, c = $4 in
         let sorted_c = List.sort (fun (i, x, t) (j, y, s) -> compare i j) c in
         let indices = List.map (fun (i, x, t) -> i) sorted_c in
         let cases = List.map (fun (i, x, t) -> (x,t)) sorted_c in
         let n = List.length (Type.Data.constructor_names id) in
         (* Check that there is a case for all constructors *)
         if (indices = Listutil.init n (fun i -> i)) then
           mkTerm (CaseW(id, $2, cases))
         else
           error "case must match each constructor exactly once!"
       }
    | termW_constr 
       { let id, i = $1 in mkTerm (InW(id, i, mkTerm UnitW)) }
    | termW_constr termW_atom
       { let id, i = $1 in mkTerm (InW(id, i, $2)) }
    | termW_app
       { $1 } 

termW_constr:
    | TokConstr
       { try Type.Data.find_constructor $1 
           with Not_found -> 
             (* TODO: message *)
             error (Printf.sprintf "Undefined constructor %s" $1)
       }

term_case:
    | termW_constr TokRightArrow 
       { let id, i = $1 in (id, i, unusable_var) }
    | termW_constr TokLParen identifier TokRParen TokRightArrow 
       { let id, i = $1 in (id, i, $3) }

termW_cases:
    | term_case termW
       { let id, i, x = $1 in (id, [i,x,$2]) } 
    | term_case termW TokVertbar termW_cases
       {  let id, i, x = $1 in
          let id', r = $4 in
            if id = id' then (id, (i, x, $2)::r) 
            else error "Constructors from different types used in case." } 

termW_app:
    | termW_atom 
       { $1 }
    | termW_app termW_atom 
       { mkTerm (AppW($1, $2))  }

termW_atom:
    | identifier
       { mkTerm (Term.Var($1)) }
    | TokLParen TokRParen 
       { mkTerm UnitW }
    | TokLParen termW TokRParen
       { $2 }
    | TokLParen termW TokComma termW TokRParen
       { mkTerm (PairW($2, $4)) }
    | TokKwPrint TokString
       { mkTerm (ConstW(Cprint $2)) } 
    | TokNum
       { mkTerm (ConstW(Cintconst($1))) } 
    | termW_atom TokPlus termW_atom
       { mkTerm (AppW(mkTerm (AppW(mkTerm (ConstW(Cintadd)), $1)), $3)) }
    | termW_atom TokMinus termW_atom
       { mkTerm (AppW(mkTerm (AppW(mkTerm (ConstW(Cintsub)), $1)), $3)) }
    | termW_atom TokTimes termW_atom
       { mkTerm (AppW(mkTerm (AppW(mkTerm (ConstW(Cintmul)), $1)), $3)) }
    | termW_atom TokDiv termW_atom
       { mkTerm (AppW(mkTerm (AppW(mkTerm (ConstW(Cintdiv)), $1)), $3)) }
    | TokLParen termW TokColon typeW TokRParen
       { mkTerm (TypeAnnot($2, Some $4)) }

dataW:
    | TokKwType datadeclW TokEquals constructorsW
      { let id, params = $2 in
        let cons = $4 in
        let n = List.length params in
          Type.Data.make id n; 
          List.iter (fun (cname, cargty) -> 
                      Type.Data.add_constructor id cname params cargty)
          cons;
          id
       }

datadeclW:
    | identifier
      { $1, [] }
    | identifier TokLAngle dataparamsW TokRAngle 
      { let ty = $1 in
        let params = $3 in
          ty, params }

dataparamsW:      
    | TokQuote identifier
      { [type_var $2] }
    | TokQuote identifier TokComma dataparamsW
      { let var = type_var $2 in
        let vars = $4 in
          if List.exists (fun alpha -> Type.equals var alpha) vars then
             error "Type variable appears twice in parameter list."
          else 
             var::vars }

constructorsW:
    | TokConstr TokKwOf typeW
      { [$1, $3] }
    | TokConstr TokKwOf typeW TokVertbar constructorsW
      { ($1, $3) :: $5 }

typeW:
    | typeW_summand
      { $1 }
    | typeW_summand TokRightArrow typeW
      { Type.newty (Type.FunW($1, $3)) } 

typeW_summand:
    | typeW_factor
      { $1 }
    | typeW_summand TokPlus typeW_factor
      { Type.newty (Type.DataW(Type.Data.sumid 2, [$1; $3])) }

typeW_factor:
    | typeW_atom
      { $1 }
    | typeW_factor TokTimes typeW_atom
      { Type.newty (Type.TensorW($1, $3)) }

typeW_atom:
    | TokQuote identifier
      { type_var $2 }
    | TokCont TokLAngle typeW TokRAngle
      { Type.newty (Type.ContW($3)) } 
    | TokKwUnit
      { Type.newty (Type.OneW) }
    | TokKwNat
      { Type.newty (Type.NatW) }
    | identifier
      { Type.newty (Type.DataW($1, [])) }
    | identifier TokLAngle typeW_list TokRAngle 
      { Type.newty (Type.DataW($1, $3)) }
    | TokLParen typeW TokRParen
      { $2 }

typeW_list:
    | typeW 
      { [$1] }
    | typeW typeW_list
      { $1 :: $2 }

termU:    
    | TokLambda identifier TokRightArrow termU 
       { mkTerm (LambdaU(($2, None), $4)) }
    | TokLambda TokLParen identifier TokColon typeU TokRParen TokRightArrow termU 
       { mkTerm (LambdaU (($3, Some $5), $8)) }
    | TokKwHack termW TokAs typeU
       { mkTerm (HackU(Some $4, $2)) }
    | TokLet TokLParen identifier TokComma identifier TokRParen TokEquals termU TokIn termU
       { mkTerm (LetU($8, ($3, $5, $10))) }
    | TokLet TokLBracket identifier TokRBracket TokEquals termU TokIn termU
       { mkTerm (LetBoxU($6, ($3, $8))) }
    | TokKwCopy termU TokAs identifier TokComma identifier TokIn termU
       { mkTerm (CopyU($2, ($4, $6, $8))) }
    | TokCase termW TokKwOf termU_cases
       { let id, c = $4 in
         let sorted_c = List.sort (fun (i, x, t) (j, y, s) -> compare i j) c in
         let indices = List.map (fun (i, x, t) -> i) sorted_c in
         let cases = List.map (fun (i, x, t) -> (x,t)) sorted_c in
         let n = List.length (Type.Data.constructor_names id) in
         (* Check that there is a case for all constructors *)
         if (indices = Listutil.init n (fun i -> i)) then
           mkTerm (CaseU(id, $2, cases))
         else
           error "case must match each constructor exactly once!"
       }
    | TokKwIf termW TokKwThen termU TokKwElse termU
       { mkTerm (CaseU(Type.Data.boolid, $2, [(unusable_var, $4); (unusable_var, $6)])) }
    | termU_app
       { $1 }

termU_cases:
    | term_case termU
       { let id, i, x = $1 in (id, [i,x,$2]) } 
    | term_case termU TokVertbar termU_cases
       {  let id, i, x = $1 in
          let id', r = $4 in
            if id = id' then (id, (i, x, $2)::r) 
            else error "Constructors from different types used in case." } 

termU_app:
    | termU_atom 
       { $1 }
    | termU_app termU_atom 
       { mkTerm (AppU($1, $2)) }

termU_atom:
    | identifier
       { mkTerm (Term.Var($1)) }
    | TokLParen termU TokComma termU TokRParen 
       { mkTerm (PairU($2, $4)) }
    | TokLBracket termW TokRBracket
       { mkTerm (BoxTermU($2)) }
    | TokLParen termU TokRParen
       { $2 }
    | TokLParen termU TokColon typeU TokRParen
       { mkTerm (TypeAnnot($2, Some $4)) }
    | TokMemo termU_atom
       { mkTerm (MemoU($2)) }
    | TokForce termU_atom
       { mkTerm (ForceU($2)) }
    | TokSuspend termU_atom
       { mkTerm (SuspendU($2)) }

typeU:
    | typeU_factor
      { $1 }
    | TokLBrace typeW TokRBrace typeU_factor TokLolli typeU
      { Type.newty (Type.FunU($2, $4, $6)) }
    | typeU_factor TokMulti typeU
      { Type.newty (Type.FunU(Type.newty Type.Var, $1, $3)) }

typeU_factor:
    | typeU_atom
      { $1 }
    | typeU_factor TokTimes typeU_atom
      {  Type.newty (Type.TensorU($1, $3)) }

typeU_atom:
    | TokQuote identifier
      { type_var $2 }
    | TokLBracket typeW TokRBracket
      {  Type.newty (Type.BoxU(Type.newty Type.OneW, $2)) }
    | TokLParen typeU TokRParen
      { $2 }
%%
