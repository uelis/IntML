open Term
open Evaluation
open Compile
open Unify

(** Returns a list of graphs with highlighted edges together with the token that 
  * is just being passed along that edge. *)
let termW_of_circuit (nsteps: int) (token: Term.t) (c: circuit) = 
  (* Rename the wires so that the output wire has label 0 *)
  let pi i = if i = 0 then c.output.dst else if i = c.output.dst then 0 else i in 
  let c' = { output = map_wire pi c.output;
             instructions = List.map (map_instruction pi) c.instructions} in
  (* Information about the wires in the graph *)
  let all_wires = wires c'.instructions in
  let max_wire_src_dst = 
    List.fold_right (fun w m -> max w.src (max w.dst m)) all_wires 0 in
  (* Message passing term *)
  let mp_term = message_passing_term c' in
  let rec step (w, token) = 
    match eval_closed (mkAppW mp_term (in_k w (max_wire_src_dst + 1) token)) with
      | None -> failwith ""
      | Some v -> out_k v (max_wire_src_dst + 1)
    in
  let rec sim i (w, token) =
    if nsteps <= i then [(i, (w, token))] else
      (i, (w, token)) :: (sim (i + 1) (step (w, token))) in
  let wire_src_type s = 
    match List.filter (fun w -> w.src = s) (all_wires) with
      | w :: _ -> w.type_forward 
      | _ -> c'.output.type_forward
  in 
  let trace = sim 0 (0, mkPairW mkUnitW token) in
  let graph_title token ty = (Printing.string_of_termW token) in
    List.map (fun (i, (w, token)) -> 
                dot_of_circuit c' 
                  ~title:(graph_title token (wire_src_type w))
                  ~wire_style:(fun v -> 
                                 if v.src = w then "[penwidth=7, color=blue]" 
                                 else "")) trace

module U = Unify(struct type t = unit end)

let simulate (nsteps: int) (t: Term.t) (token: Term.t) =
  Printf.printf "compiling graph...\n"; flush stdout;
  let circuit = circuit_of_termU [] [] t in
  Printf.printf "typing graph...\n"; flush stdout;
  let a = Compile.infer_types circuit in
  let annotated_token = fresh_vars_for_missing_annots token in
    
  (* unify input type of circuit with type of token *)
  let circuit_input_type = 
    match Type.finddesc a with
      | Type.FunW(b, _) -> b
      | _ -> assert false in
  let token_type = Typing.principal_typeW [] annotated_token in
  let _  = 
    try
      U.unify circuit_input_type token_type 
    with 
      | U.Not_Unifiable _ -> 
	  let msg = "Token type (" ^ Printing.string_of_type token_type ^
	    ") and the input type of the circuit (" ^ 
	    Printing.string_of_type circuit_input_type ^ 
	    ") cannot be unified." in
	  raise (Typing.Typing_error(None, msg))
  in
    
  (* trace the (now closed) through the (now closed) circuit *)
  Printf.printf "compiling to term...\n"; flush stdout;  
  let exec_trace = termW_of_circuit nsteps annotated_token circuit in
  Printf.printf "done\n"; flush stdout;
    exec_trace

