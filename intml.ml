open Lexing
open Opts
open Decls
open Term
open Term.Location
open Printing

(* Xavier Leroy posted this on the OCaml mailing list *)
let read_file filename =
   let ic = open_in_bin filename in
   let len = in_channel_length ic in
   let s = String.create len in
   really_input ic s 0 len;
   close_in ic;
   s

let write_file filename s = 
  let oc = open_out filename in 
    Printf.fprintf oc "%s" s;
    close_out oc

let parse_error_loc lexbuf =
  let start_pos = lexbuf.lex_start_p in
    Printf.sprintf "line %i, character %i:"
      (start_pos.pos_lnum) (start_pos.pos_cnum - start_pos.pos_bol + 1)

let parse (s: string) : decls =
  let lexbuf = Lexing.from_string s in
    try 
      Parser.decls Lexer.main lexbuf
    with 
      | Parsing.Parse_error -> 
          failwith (Top.error_msg (parse_error_loc lexbuf) "Parse error")
      | Decls.Non_Wellformed(msg, l, c) -> 
          failwith (Top.error_msg (Top.line_column_loc l c) ("Syntax error. " ^ msg))

let parse_query (s: string) : Query.query =
  let lexbuf = Lexing.from_string s in
    try 
      Parser.top_query Lexer.main lexbuf
    with 
      | Parsing.Parse_error -> 
          failwith (Top.error_msg (parse_error_loc lexbuf) "Parse error")
      | Decls.Non_Wellformed(msg, l, c) -> 
          failwith (Top.error_msg (Top.line_column_loc l c) ("Syntax error. " ^ msg))

let rec compile_passes (d: typed_decls) : unit = 
  match d with
    | [] -> ()
    | TypedTermDeclW(_, _, _) :: r -> compile_passes r
    | TypedTermDeclU(f, t, _) :: r -> 
        let circuit = Circuit.circuit_of_termU t in
          if !opt_keep_circuits then
            begin
              let target = Printf.sprintf "%s.dot" f in
              Printf.printf "*** Writing circuit for %s to file '%s'\n" f target;
              write_file target
                (Circuit.dot_of_circuit circuit)
            end;
          if !opt_compile_to_terms then
            begin
              let target = Printf.sprintf "%s.wc" f in
              Printf.printf "*** Writing circuit for %s to file '%s'\n" f target;
              let term, _ = Termcodegen.termW_of_circuit circuit in
              write_file target
                (Printing.string_of_termW term)
            end;
          if !opt_keep_ssa || !opt_llvm_compile then
            begin
              let ssa_func = Ssa.trace f circuit in
              if !opt_keep_ssa then
                begin
                  let target = Printf.sprintf "%s.ssa" f in
                    Printf.printf "*** Writing ssa-form program for %s to file '%s'\n" f target;
                    write_file target
                      (Ssa.string_of_func ssa_func)
                end;
              if !opt_llvm_compile then
                begin
                  let target = Printf.sprintf "%s.bc" f in
                    Printf.printf "*** Writing llvm bitcode for %s to file '%s'\n" f target;
                    let llvm_module = Llvmcodegen.llvm_compile ssa_func in
                      ignore (Llvm_bitwriter.write_bitcode_file llvm_module target)
                end
            end;
          compile_passes r

let rec eval_loop (ds: typed_decls) : unit =
  Printf.printf "\n# ";
  let input = try read_line () with End_of_file -> print_string "\n"; exit 0 in   
  let ds = try 
    Top.exec_query ds (parse_query input)
  with 
    | Failure msg -> Printf.printf "%s\n" msg; ds
    | Typing.Typing_error(s, err) -> 
        Top.print_error (Top.term_loc s) (Printf.sprintf "Type error:\n%s\n" err);
        ds 
  in
    eval_loop ds

let arg_spec =     
  [("--type-details", 
    Arg.Unit (fun _ -> opt_print_type_details := true), 
    "Print the upper class types in full detail, rather than showing just an abbreviated type.");
   ("--circuits", 
    Arg.Unit (fun _ -> opt_keep_circuits := true), 
    "Write the circuit for each upper class declaration into a file in dot format.");
   ("--ssa", 
    Arg.Unit (fun _ -> opt_keep_ssa := true), 
    "Write the ssa-form program for each upper class declaration into a file in dot format.");
   ("--compiled-terms", 
    Arg.Unit (fun _ -> opt_compile_to_terms := true), 
    "Write a term implementing the message passing circuit for each upper class declaration into a file.");
   ("--llvm", 
    Arg.Unit (fun _ -> opt_llvm_compile := true), 
    "Compile upper class programs to LLVM bitcode.");
   ]

let usage_msg = "First argument must be the name of a file containing definitions."  

let main = 
try 
  print_string "IntML\n";
  let file_name = ref "" in
    Arg.parse arg_spec (fun s -> file_name := s) usage_msg;
    let typed_decls =
      if !file_name = "" then []
      else begin
        Printf.printf "\nReading file '%s'.\n\n" !file_name;
        let input = read_file !file_name in
        let decls = parse input in
        let substituted_decls = subst_decls decls in
        let typed_decls = List.fold_left Top.new_decl [] substituted_decls in
          compile_passes typed_decls;
          typed_decls
      end 
    in 
      if not (!opt_llvm_compile || !opt_compile_to_terms || 
              !opt_keep_circuits || !opt_keep_ssa) then
        eval_loop typed_decls
with 
  | Failure msg -> Printf.printf "%s\n" msg
  | Typing.Typing_error(t, msg)-> Top.print_error (Top.term_loc t) msg

