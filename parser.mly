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

let error pos msg =
    print_string msg;
    Printf.printf " at position %i.\n"
        (pos.pos_cnum - pos.pos_bol + 1);
    flush stdout;
    raise Exit

let mkTerm d : Term.t =
  let s = Parsing.symbol_start_pos () in 
  let e = Parsing.symbol_end_pos () in 
  let lp pos = {
    Location.line = pos.pos_lnum; 
    Location.column = pos.pos_cnum - pos.pos_bol + 1 } in
  { Term.desc = d; loc = Some({Location.start_pos = lp s; Location.end_pos = lp e }) } 

let warn msg =
  let s = Parsing.symbol_start_pos () in 
  Printf.printf "Warning: %s in line %i\n" msg s.pos_lnum

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
%token TokTimes
%token TokComma
%token TokQuote
%token TokColon
%token TokSemicolon
%token TokSharp
%token TokEquals
%token TokKwIf
%token TokKwThen
%token TokKwElse
%token TokKwPrint
%token TokKwMin
%token TokKwSucc
%token TokKwEq
%token TokKwHack
%token TokLoop
%token TokZero
%token TokOne
%token TokLet 
%token TokAs
%token TokOf 
%token TokIn 
%token TokKwCopy
%token TokCase
%token TokKwInl 
%token TokKwInr 
%token TokLetW
%token TokLetU
%token TokLolli
%token TokMulti
%token TokVertbar
%token <int> TokNum
%token <string> TokIdent 
%token <string> TokString 
%token TokEof

%start decls
%start top_query
%type <Decls.decls> decls
%type <Top.query> top_query
%type <Type.t> typeW
%type <Type.t> typeU

%%

top_query: 
    | termW TokEof
      { Top.DirTerm("eval", $1) }
    | decl TokEof
      { Top.DirDecl("decl", $1) }
    | TokSharp TokIdent TokEof
      { Top.Dir($2) }
    | TokSharp TokIdent termU_atom TokEof
      { Top.DirTerm($2, $3) }
    | TokSharp TokIdent termU_atom termW TokEof
      { Top.DirTerm2($2, $3, $4) }
    | TokSharp TokIdent TokNum TokEof
      { Top.DirInt($2, $3) }

decls:
    | TokEof
      { [] }
    | decl decls
      { $1 :: $2 }

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
    | TokLet TokLAngle identifier TokComma identifier TokRAngle TokEquals termW TokIn termW
      { mkTerm (LetW($8, ($3, $5, $10))) }
    | TokKwIf termW TokKwThen termW TokKwElse termW
      { mkTerm (CaseW($2, [(unusable_var, $4); (unusable_var, $6)])) }
    | TokCase termW TokOf 
          TokKwInl TokLParen identifier TokRParen TokRightArrow termW 
          TokVertbar
          TokKwInr TokLParen identifier TokRParen TokRightArrow termW
       { mkTerm (CaseW($2, [($6, $9); ($13, $16)])) }
    | TokLet identifier TokEquals termW TokLoop termW
       { mkTerm (AppW (mkTerm (TrW (mkLambdaW(($2, None), mkCaseW (mkVar $2) [($2, mkInrW (mkVar $2)); ($2, $6)]))), $4)) }
    | TokLet identifier TokEquals termW TokIn termW
       { mkTerm (AppW (mkTerm (LambdaW(($2, None), $6)), $4)) }
    | TokLet TokLBracket identifier TokRBracket TokEquals termU TokIn termW
       { mkTerm (LetBoxW($6, ($3, $8))) }
    | termW_app TokSemicolon termW
       { mkTerm (AppW (mkTerm (LambdaW((unusable_var, Some (Type.newty Type.OneW)), $3)), $1)) }
    | termW_app
       { $1 } 

termW_app:
    | termW_atom 
       { $1 }
    | termW_app termW_atom 
       { mkTerm (AppW($1, $2))  }
    | termW_app TokEquals termW_atom
       { mkTerm (AppW(mkTerm (AppW(mkTerm (ConstW(None, Ceq)), $1)), $3)) }

termW_atom:
    | identifier
       { mkTerm (Term.Var($1)) }
    | TokLAngle TokRAngle 
       { mkTerm UnitW }
    | TokLParen termW TokRParen
       { $2 }
    | TokLAngle termW TokComma termW TokRAngle 
       { mkTerm (PairW($2, $4)) }
    | TokKwInl TokLParen termW TokRParen
       { mkTerm (InW(2, 0, $3)) }
    | TokKwInr TokLParen termW TokRParen
       { mkTerm (InW(2, 1, $3)) }
    | TokKwPrint TokString
       { mkTerm (ConstW(None, Cprint $2)) } 
    | TokKwMin
       { mkTerm (ConstW(None, Cmin)) } 
    | TokKwSucc
       { mkTerm (ConstW(None, Csucc)) }
    | TokKwEq
       { mkTerm (ConstW(None, Ceq)) }
    | TokLParen termW TokColon typeW TokRParen
       { match $2.desc with
         | ConstW(None, c) -> {$2 with desc = ConstW(Some $4, c)}
         | _ ->  mkTerm (TypeAnnot($2, Some $4)) }

typeW:
    | typeW_summand
      { $1 }
    | typeW_summand TokRightArrow typeW
      { Type.newty (Type.FunW($1, $3)) } 

typeW_summand:
    | typeW_factor
      { $1 }
    | typeW_summand TokPlus typeW_factor
      { Type.newty (Type.SumW[$1; $3]) }

typeW_factor:
    | typeW_atom
      { $1 }
    | typeW_factor TokTimes typeW_atom
      { Type.newty (Type.TensorW($1, $3)) }

typeW_atom:
    | TokQuote identifier
      { type_var $2 }
    | TokNum 
      { let rec nat_ty n = 
          match n with
          | 0 -> Type.newty (Type.ZeroW)
          | 1 -> Type.newty (Type.OneW)
          | 2 -> Type.newty (Type.SumW[Type.newty (Type.OneW); Type.newty (Type.OneW)])
          | n -> if n mod 2 = 0 then              
                   Type.newty (Type.TensorW (nat_ty (n/2), nat_ty 2))
                 else
                   Type.newty (Type.SumW [nat_ty (n-1); nat_ty 1])
        in  nat_ty $1
      }
    | TokLParen typeW TokRParen
      { $2 }

termU:    
    | TokLambda identifier TokRightArrow termU 
       { mkTerm (LambdaU(($2, None), $4)) }
    | TokLambda TokLParen identifier TokColon typeU TokRParen TokRightArrow termU 
       { mkTerm (LambdaU (($3, Some $5), $8)) }
    | TokKwHack termW TokAs typeU
       { mkTerm (HackU(Some $4, $2)) }
    | TokLet TokLAngle identifier TokComma identifier TokRAngle TokEquals termU TokIn termU
       { mkTerm (LetU($8, ($3, $5, $10))) }
    | TokLet TokLBracket identifier TokRBracket TokEquals termU TokIn termU
       { mkTerm (LetBoxU($6, ($3, $8))) }
    | TokKwCopy termU TokAs identifier TokComma identifier TokIn termU
       { mkTerm (CopyU($2, ($4, $6, $8))) }
    | TokCase termW TokOf 
          TokKwInl TokLParen identifier TokRParen TokRightArrow termU 
          TokVertbar
          TokKwInr TokLParen identifier TokRParen TokRightArrow termU
       { mkTerm (CaseU($2, ($6, $9), ($13, $16))) } 
    | TokKwIf termW TokKwThen termU TokKwElse termU
       { mkTerm (CaseU($2, (unusable_var, $4), (unusable_var, $6))) }
    | termU_app
       { $1 }

termU_app:
    | termU_atom 
       { $1 }
    | termU_app termU_atom 
       { mkTerm (AppU($1, $2)) }

termU_atom:
    | identifier
       { mkTerm (Term.Var($1)) }
    | TokLAngle termU TokComma termU TokRAngle 
       { mkTerm (PairU($2, $4)) }
    | TokLBracket termW TokRBracket
       { mkTerm (BoxTermU($2)) }
    | TokLParen termU TokRParen
       { $2 }
    | TokLParen termU TokColon typeU TokRParen
       { mkTerm (TypeAnnot($2, Some $4)) }

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
