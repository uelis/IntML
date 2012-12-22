type wire = {
  src: int;
  dst: int;
  type_forward: Type.t;
  type_back: Type.t
}

type instruction =
    Axiom of wire (* [f] *) * (Term.var list * Term.t)
  | Tensor of wire (* X *) * wire (* Y *) * wire (* X \otimes Y *)
  | Der of wire (* \Tens A X *) * wire (* X *) * (Term.var list * Term.t)
  | Case of Type.Data.id * wire * (wire list)
  | Door of wire (* X *) * wire (* \Tens A X *)
  | ADoor of wire (* \Tens (A x B) X *) * wire (* \Tens B X *) 
  | LWeak of wire (* \Tens A X *) * wire (* \Tens B X *) (* where B <= A *)
  | Epsilon of wire (* [A] *) * wire (* \Tens A [B] *) * wire (* [B] *)
  | Memo of wire (* X *) * wire (* X *)
  | Grab of Term.var list * wire (* X *) * wire
  | Force of wire (* X *) * (Term.var list * Term.t)

type circuit = { 
  output : wire; 
  instructions : instruction list
}

val map_wire : (int -> int) -> wire -> wire                 
val map_instruction : (int -> int) -> instruction -> instruction                  
val wires : instruction list -> wire list

val circuit_of_termU : Term.t -> circuit

val dot_of_circuit :
 ?title:string -> ?wire_style:(wire -> string) -> circuit -> string
