open Lexing
open Opts
open Decls
open Term
open Term.Location
open Printing
open Compile 

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

let parse_query (s: string) : Top.query =
  let lexbuf = Lexing.from_string s in
    try 
      Parser.top_query Lexer.main lexbuf
    with 
      | Parsing.Parse_error -> 
          failwith (Top.error_msg (parse_error_loc lexbuf) "Parse error")

let rec print_graphs (d: typed_decls) : unit = 
  match d with
    | [] -> ()
    | TypedTermDeclW(_, _, _) :: r -> print_graphs r
    | TypedTermDeclU(f, t, _) :: r -> 
        Printf.printf "*** Writing graph for %s to file '%s.dot' ***\n" f f;
        flush stdout;
        let graph = circuit_of_termU [] [] t in
        let _ = infer_types graph in
        let dot_graph = dot_of_circuit graph in
        let oc = open_out (Printf.sprintf "%s.dot" f) in 
          Printf.fprintf oc "%s\n" dot_graph;
          close_out oc;
          print_graphs r

let rec print_compiled_terms (d: typed_decls) : unit = 
  match d with
    | [] -> ()
    | TypedTermDeclW(_, _, _) :: r -> print_compiled_terms r
    | TypedTermDeclU(f, t, _) :: r -> 
        Printf.printf "*** Writing compiled term for '%s' to file '%s.wc' ***\n" f f;
          flush stdout;
          let oc = open_out (Printf.sprintf "%s.wc" f) in 
            Printf.fprintf oc "%s\n" (prg_termU t);
            close_out oc;
            print_compiled_terms r

let rec llvm_compile (d: typed_decls) : unit = 
  match d with
    | [] -> ()
    | TypedTermDeclW(_, _, _) :: r -> llvm_compile r
    | TypedTermDeclU(f, t, ty) :: r -> 
        (* compile only terms of box type *)
        (match Type.finddesc ty with
          | Type.BoxU(q, a) ->              
              (match Type.finddesc q with
                 | Type.OneW ->
                    Printf.printf "*** Writing llvm bytecode for '%s' to file '%s.bc' ***\n" f f;
                    flush stdout;
                    let graph = circuit_of_termU [] [] t in
                    let _ = infer_types graph in 
                    let llvm_module = Llvmcodegen.llvm_circuit graph in
                      ignore (Llvm_bitwriter.write_bitcode_file llvm_module (Printf.sprintf "%s.bc" f))
                 | _ -> ())
           | _ -> ());
        llvm_compile r

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

(* Xavier Leroy posted this on the OCaml mailing list *)
let read_input filename =
   let ic = open_in_bin filename in
   let len = in_channel_length ic in
   let s = String.create len in
   really_input ic s 0 len;
   close_in ic;
   s

let arg_spec =     
  [("--type-details", 
    Arg.Unit (fun _ -> opt_print_type_details := true), 
    "Print the upper class types in full detail, rather than showing just an abbreviated type.");
   ("--circuits", 
    Arg.Unit (fun _ -> opt_print_graphs := true), 
    "Write the circuit for each upper class declaration into a file in dot format.");
   ("--compiled-terms", 
    Arg.Unit (fun _ -> opt_print_compiled_terms := true), 
    "Write the compiled term for each upper class declaration into a file.");
   ("--llvm", 
    Arg.Unit (fun _ -> opt_llvm_compile := true), 
    "Compile upper class programs of type [A] to LLVM bitcode.");
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
        let input = read_input !file_name in
        let decls = parse input in
        let substituted_decls = subst_decls decls in
        let typed_decls = List.fold_left Top.new_decl [] substituted_decls in
          if !opt_print_compiled_terms then print_compiled_terms typed_decls;
          if !opt_llvm_compile then llvm_compile typed_decls;
          if !opt_print_graphs then print_graphs typed_decls;
          typed_decls
      end 
    in 
      eval_loop typed_decls
with 
  | Typing.Typing_error(t, msg)-> Top.print_error (Top.term_loc t) msg

