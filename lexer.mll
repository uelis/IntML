(************************************************************************
*
*  lexer.mll
*
*
************************************************************************)

{
open Parser
open Lexing

let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }

let error lexbuf msg =
       let pos = lexbuf.Lexing.lex_curr_p in
       print_string msg;
       Printf.printf " at position %i.\n" (pos.pos_cnum - pos.pos_bol);
       flush stdout;
       raise Parsing.Parse_error
}

let white = [' ' '\t']+
let num = ['0'-'9']
let alpha = ['a'-'z'] | ['A'-'Z'] | '\\'
let nat = num*
let ident =  ['a'-'z'] (alpha | num | '_' | ''' )*
let constr =  ['A'-'Z'] (alpha | num | '_' | ''' )*

rule main = parse
  | '\n'       { incr_linenum lexbuf; main lexbuf }
  |  white     { main lexbuf }
  | '('        { TokLParen }
  | ')'        { TokRParen }
  | '{'        { TokLBrace }
  | '}'        { TokRBrace }
  | '<'        { TokLAngle }
  | '>'        { TokRAngle }
  | "->"       { TokRightArrow }
  | '['        { TokLBracket }
  | ']'        { TokRBracket }
  | "fun"      { TokLambda }
  | '+'        { TokPlus }
  | '-'        { TokMinus }
  | '*'        { TokTimes }
  | '/'        { TokDiv }
  | ','        { TokComma }
  | '.'        { TokDot }
  | '''        { TokQuote }
  | ':'        { TokColon }
  | ';'        { TokSemicolon }
  | '#'        { TokSharp }
  | '='        { TokEquals }
  | ":="       { TokColonEquals }
  | "type"     { TokType }
  | "mutable"  { TokMutable }
  | "unit"     { TokUnit }
  | "delete"   { TokDelete }
  | "if"       { TokIf }
  | "then"     { TokThen }
  | "else"     { TokElse }
  | "print"    { TokPrint }
  | "int"      { TokNat }
  | "eq"       { TokEq }
  | "hack"     { TokHack }
  | "copy"     { TokCopy }
  | "let"      { TokLet }
  | "as"       { TokAs }
  | "of"       { TokOf }
  | "in"       { TokIn }
  | "case"     { TokCase }
  | "loop"     { TokLoop }
  | "letw"     { TokLetW }
  | "letu"     { TokLetU }
  | "invokec"    { TokForce }
  | "grabc"    { TokSuspend }
  | "cont"     { TokCont }
  | "external" { TokExternal }
  | "--o"      { TokLolli }
  | "-->"      { TokMulti }
  | "|"        { TokVertbar }
  | nat        { TokNum (int_of_string (Lexing.lexeme lexbuf)) }
  | ident      { TokIdent (Lexing.lexeme lexbuf) }
  | constr     { TokConstr (Lexing.lexeme lexbuf) }
  | eof        { TokEof } 
  | "(*"       { comments 0 lexbuf}
  | "\""       { let buf = Buffer.create 1 in
                    TokString (str buf lexbuf)}
  | _          { error lexbuf "Unexpected symbol" }
and comments level = parse
  | '\n'       { incr_linenum lexbuf; comments level lexbuf }
  | "(*"       { comments (level+1) lexbuf }
  | "*)"       { if level = 0 then main lexbuf else comments (level-1) lexbuf }
  | _          { comments level lexbuf }
  | eof        { print_endline "comments are not closed";
                raise End_of_file }
and str buf = parse
  | '"'        { Buffer.contents buf }
  | "\\n"      { Buffer.add_char buf '\n'; str buf lexbuf }
  | "\\\""     { Buffer.add_char buf '"'; str buf lexbuf }
  | _ as ch    { Buffer.add_char buf ch; str buf lexbuf }

