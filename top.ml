open Opts
open Decls
open Printing
open Term
open Term.Location
open Typing
open Evaluation
open Compile

type query = 
  | Dir of string
  | DirTerm of string * Term.t
  | DirDecl of string * Decls.decl
  | DirTerm2 of string * Term.t * Term.t
  | DirType of string * Type.t
  | DirInt of string * int

let sim_length = ref 10

let error_msg loc msg = loc ^ "\n" ^ msg
let print_error loc msg = print_string (error_msg loc msg)

(* For error reporting: compute a string of where the error occurred *)
let term_loc (s : Term.t option) = 
  match s with
    | None -> ""
    | Some s ->
        match s.loc with
          | Some(loc) when loc.start_pos.line = loc.end_pos.line -> 
              Printf.sprintf "line %i, columns %i-%i:" 
                loc.start_pos.line loc.start_pos.column loc.end_pos.column
          | Some(loc) -> 
              Printf.sprintf "line %i, column %i to line %i, column %i:" 
                loc.start_pos.line loc.start_pos.column
                loc.end_pos.line loc.end_pos.column
          | None -> "Term " ^ (Printing.string_of_termW s) 

let rec new_decl (ds : typed_decls) (d : decl) : typed_decls =
  Printing.reset_names ();
  flush stdout;
  match d with
    | TermDeclW(f, t) ->
        begin 
          try 
            let t_with_type_annots = Term.fresh_vars_for_missing_annots t in
            let a = Typing.principal_typeW [] t_with_type_annots in
              Printf.printf "%s :w %s" f (string_of_type a);
              (match (Evaluation.eval_closed t_with_type_annots) with
                 | Some v -> Printf.printf " = %s\n" (string_of_termW v)
                 | None -> Printf.printf "\n");
              ds @ [TypedTermDeclW(f, t_with_type_annots, a)]
          with Typing.Typing_error(t, err) ->
            let msg = "Typing error when checking working " ^
                      "class declaration of '" ^ f ^ "'.\n" ^ err ^ "\n" in
              raise (Failure (error_msg (term_loc t) msg))
        end
    | TermDeclU(f, t) ->
        try 
          let b = Typing.principal_typeU [] [] t in
          let b_str = 
            if !opt_print_type_details then
              string_of_type b
            else 
              abstract_string_of_typeU b
          in
            Printf.printf "%s :u %s\n" f b_str;
            ds @ [TypedTermDeclU(f, t, b)]
        with Typing.Typing_error(s, err) ->
          let msg = "Typing error when checking upper " ^
                    "class declaration of '" ^ f ^ "'.\n" ^ err ^ "\n" in
              raise (Failure (error_msg (term_loc s) msg))


let rec exec_query (ds: typed_decls) (q: query) : typed_decls =
  Printing.reset_names ();
  match q with
    | Dir("eval") ->
        Printf.printf "#eval expects as arguments a term that should be evaluated.\n";
        ds
    | DirTerm("eval", query) ->
        let term = Term.fresh_vars_for_missing_annots query in
        let closed_query = List.fold_right subst_typed_decl_in_term ds term in
        let closed_query_type = principal_typeW [] closed_query in
          Printf.printf ": %s\n" (string_of_type closed_query_type);
          flush stdout;
          let result = 
            match eval_closed closed_query with
              | Some v -> string_of_termW v
              | None -> "functional value"
          in 
            Printf.printf "\n= %s\n" result;
            ds
    | Dir("decl") ->
        Printf.printf "#decl expects as arguments a declaration that should be evaluated.\n";
        ds
    | DirDecl("decl", d) ->
        let substituted_decl = 
          List.fold_right subst_typed_decl_in_decl ds d in
        new_decl ds substituted_decl
    | Dir("simlength") ->
        Printf.printf "The current value of #simstep is %i.\n" !sim_length;
        Printf.printf "It specifies how many steps simulations are run for.\n";
        ds
    | DirInt("simlength", i) ->
        Printf.printf "Setting number of simulation steps to %i.\n" i;
        sim_length := i;
        ds
    | Dir("circuit") ->
        Printf.printf "#circuit expects arguments in the following form:\n";
        Printf.printf " #circuit (upper class term) \n";
        Printf.printf " #circuit (upper class term) (token)\n";
        Printf.printf "For circuit one may use arbitrarty upper class terms,\n";
        Printf.printf "which are compiled to circuits automatically.";
        ds
    | Dir("sim") | DirTerm("sim", _) ->
        Printf.printf "#sim expects arguments in the following form:\n";
        Printf.printf " #sim (upper class term) (token)\n";
        Printf.printf "For circuit one may use the names of upper class terms,\n";
        Printf.printf "which are compiled to circuits automatically.";
        ds
    | DirTerm("circuit", circuit) ->
        let circuit = List.fold_right subst_typed_decl_in_term ds circuit in
        let _ = Typing.principal_typeU [] [] circuit in
        let _, circuitW_type = compile_termU circuit in
          Printf.printf ": %s\n" (string_of_type circuitW_type);
          Printf.printf "\n= functional value\n";
          ds
    | DirTerm2("circuit", circuit, token) ->
        begin 
          let circuit = List.fold_right subst_typed_decl_in_term ds circuit in
          let token = List.fold_right subst_typed_decl_in_term ds token in
          let token = Term.fresh_vars_for_missing_annots token in
          let token_type = Typing.principal_typeW [] token in
          let _ = Typing.principal_typeU [] [] circuit in
          let circuitW, circuitW_type = compile_termU circuit in
          let circuit_input_type, circuit_output_type = 
            match Type.finddesc circuitW_type with
              | Type.FunW(b, c) -> b, c
              | _ -> assert false 
          in
            try
              U.unify circuit_input_type token_type;
              Printf.printf ": %s\n" (string_of_type circuit_output_type);
              let result = 
                match eval_closed (Term.mkAppW circuitW token) with
                  | Some v -> string_of_termW v
                  | None -> "functional value"
              in 
                Printf.printf "\n= %s\n" result;
                ds
            with 
              | U.Not_Unifiable _ -> 
                  let msg = "Token type (" ^ Printing.string_of_type token_type ^
                            ") and the input type of the circuit (" ^ 
                            Printing.string_of_type circuit_input_type ^ 
                            ") cannot be unified." in
                    Printf.printf "%s" msg;
                    ds
        end
    | DirTerm2("sim", circuit, token) ->
        begin 
          let circuit = List.fold_right subst_typed_decl_in_term ds circuit in
          let _ = Typing.principal_typeU [] [] circuit in
          let token = List.fold_right subst_typed_decl_in_term ds token in
          let token = Term.fresh_vars_for_missing_annots token in
          let _ = Typing.principal_typeW [] token in
            Printf.printf "Simulating message passing...\n"; flush stdout;
            let graphs = Simulate.simulate !sim_length circuit token in
              Printf.printf "Generating pdf file...\n"; flush stdout;
              let i = ref (0: int) in
              let pdfs = ref "" in 
                List.iter 
                  (fun graph -> 
                     let oc = open_out (Printf.sprintf "/tmp/sim%i.dot" !i) in 
                       Printf.fprintf oc "%s\n" graph;
                       close_out oc;
                       let cmd = 
                         Printf.sprintf 
                           "dot -Tpdf /tmp/sim%i.dot > /tmp/sim%i.pdf" !i !i in
                       let _ = Sys.command cmd in
                         pdfs := Printf.sprintf "%s /tmp/sim%i.pdf" !pdfs !i;
                         i := !i +1) graphs;
                ignore (Sys.command ("pdftk " ^ !pdfs ^ 
                                     " cat output circuit.sim.pdf"))
        end;
        ds
    | _ -> 
        Printf.printf "Unknown command.\n";
        ds
