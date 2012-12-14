(** Printing of terms and types *)

(* TODO: 
 *  - printing of upper class terms
 *)

open Term

let name_counter = ref 0

let new_name () =
  let i = !name_counter in
  incr(name_counter);
  let c = Char.chr(Char.code 'a' + i mod 26) in
  let n = i / 26 in
   if (n = 0) then 
     Printf.sprintf "%c" c
   else
     Printf.sprintf "%c%i" c n;;

let reset_names () = 
  name_counter := 0

let name_table = Type.Typetbl.create 10   
let name_of_typevar t = 
  try
    Type.Typetbl.find name_table (Type.find t)
  with 
    | Not_found -> 
        let name = new_name() in
          Type.Typetbl.add name_table (Type.find t) name;
          name

 
(* works properly only on well-formed types *)
let string_of_type (ty: Type.t): string =  
  let buf = Buffer.create 80 in
    (* recognize loops and avoid printing infinite types *)
  let module Tbl = 
    Hashtbl.Make(
         struct
           type t = int * Type.t
           let equal (i, s) (j, t) = i=j && s == t
           let hash (i, s) = i + 7 * s.Type.id
         end) in
  let table = Tbl.create 10 in
  let check_rec (i,j) = 
    try
      let k = Tbl.find table (i,j) in
        Tbl.replace table (i,j) (k+1);
        if k > 2 then
          (Buffer.add_string buf "..."; false)
        else true
    with
       Not_found -> 
         Tbl.add table (i,j) 0;
         true
  in
  let rec s_typeW (t: Type.t) =
    if check_rec (0, t) then
    match (Type.finddesc t) with
      | Type.FunW(t1, t2) ->
          s_typeW_summand t1;
          Buffer.add_string buf " -> ";
          s_typeW t2 
      | _ -> 
          s_typeW_summand t
  and s_typeW_summand (t: Type.t) =
    if check_rec (1, t) then
    match (Type.finddesc t) with
      | Type.SumW([t1; t2]) ->
          s_typeW_summand t1; 
          Buffer.add_string buf " + ";
          s_typeW_factor t2
      | Type.SumW([]) ->
          Buffer.add_string buf "0"
      | Type.SumW(t1 :: l) ->
          Buffer.add_string buf "Sum(";
          s_typeW_summand t1;           
          List.iter (fun t2 -> s_typeW_summand t2; 
                               Buffer.add_string buf ", ") l;
          Buffer.add_string buf ")";
      | _ -> 
          s_typeW_factor t
  and s_typeW_factor (t: Type.t) =
    if check_rec (2, t) then
    match (Type.finddesc t) with
      | Type.TensorW(t1, t2) ->
          s_typeW_factor t1;
          Buffer.add_string buf " * ";
          s_typeW_atom t2
      | _ -> 
          s_typeW_atom t
  and s_typeW_atom (t: Type.t) =
    match (Type.finddesc t) with
      | Type.Var ->  
          Buffer.add_char buf '\'';
          Buffer.add_string buf (name_of_typevar t)
      | Type.NatW -> Buffer.add_string buf "int"
      | Type.ZeroW -> Buffer.add_char buf '0'
      | Type.OneW -> Buffer.add_char buf '1'
      | Type.MuW(alpha, a) ->
          Buffer.add_string buf "mu<";
          s_typeW alpha;
          Buffer.add_char buf '.';
          s_typeW a;
          Buffer.add_char buf '>'
      | Type.ContW(ret) ->
          Buffer.add_string buf "cont<";
          s_typeW ret;
          Buffer.add_char buf '>'
      | Type.FunW _ | Type.SumW _ | Type.TensorW _ ->
          Buffer.add_char buf '(';
          s_typeW t;
          Buffer.add_char buf ')';
      | Type.FunU _ | Type.TensorU _ | Type.BoxU _ ->
          s_typeU t
      | Type.Link _ -> assert false
  and s_typeU (t: Type.t) =
    if check_rec (3, t) then
    match (Type.finddesc t) with
      | Type.FunU(o, t1, t2) when (Type.finddesc o = Type.OneW) ->
          s_typeU_factor t1;
          Buffer.add_string buf " --o ";
          s_typeU t2
      | Type.FunU(a1, t1, t2) ->
          Buffer.add_char buf '{';
          s_typeW a1;
          Buffer.add_char buf '}';
          s_typeU_atom t1;
          Buffer.add_string buf " --o ";
          s_typeU t2
      | _ -> 
          s_typeU_factor t
  and s_typeU_factor (t: Type.t) =
    if check_rec (4, t) then
    match (Type.finddesc t) with
      | Type.TensorU(t1, t2) ->
          s_typeU_factor t1;
          Buffer.add_string buf " * ";
          s_typeU_atom t2
      | _ -> 
          s_typeU_atom t
  and s_typeU_atom (t: Type.t) =
    match (Type.finddesc t) with
      | Type.Var -> 
          Buffer.add_char buf '\'';
          Buffer.add_string buf (name_of_typevar t)
      | Type.BoxU(o, t2) when (Type.finddesc o = Type.OneW) ->
          Buffer.add_char buf '[';
          s_typeW t2;
          Buffer.add_char buf ']'
      | Type.BoxU(t1, t2) ->
          Buffer.add_char buf '[';
          s_typeW t1;
          Buffer.add_string buf ", ";
          s_typeW t2;
          Buffer.add_char buf ']'
      | Type.ZeroW | Type.OneW | Type.FunW _ | Type.NatW
      | Type.SumW _ | Type.TensorW _ | Type.MuW _ | Type.ContW _ ->
          s_typeW t
      | Type.FunU _ | Type.TensorU _  ->
          Buffer.add_char buf '(';
          s_typeU t;
          Buffer.add_char buf ')'
      | Type.Link _ -> assert false
  in s_typeU ty;
     Buffer.contents buf

(* Print only information that is interesting to the user, 
 * but not the details *)
let abstract_string_of_typeU (ty: Type.t): string =
  let buf = Buffer.create 80 in
  let rec s_typeU (t: Type.t) =
    match Type.finddesc t with
      | Type.FunU(o, t1, t2) when (Type.finddesc o = Type.OneW) ->
          s_typeU_factor t1;
          Buffer.add_string buf " --o ";
          s_typeU t2
      | Type.FunU(_, t1, t2) ->
          s_typeU_atom t1;
          Buffer.add_string buf " --> ";
          s_typeU t2
      | _ -> 
          s_typeU_factor t
  and s_typeU_factor (t: Type.t) =
    match Type.finddesc t with
      | Type.TensorU(t1, t2) ->
          s_typeU_factor t1;
          Buffer.add_string buf " * ";
          s_typeU_atom t2
      | _ -> (s_typeU_atom t)
  and s_typeU_atom (t: Type.t) =
    match Type.finddesc t with
      | Type.Var -> 
          Buffer.add_char buf '\'';
          Buffer.add_string buf (name_of_typevar t) 
      | Type.BoxU(o, t2) when (Type.finddesc o = Type.OneW) ->
          Buffer.add_char buf '[';
          Buffer.add_string buf (string_of_type t2);
          Buffer.add_char buf ']'
      | Type.BoxU(t1, t2) ->
          Buffer.add_char buf '[';
          Buffer.add_string buf (string_of_type t1);
          Buffer.add_string buf ", ";
          Buffer.add_string buf (string_of_type t2);
          Buffer.add_char buf ']'
      | Type.NatW | Type.ZeroW | Type.OneW | Type.FunW _
      | Type.SumW _ | Type.TensorW _ | Type.MuW _ | Type.ContW _ ->
          Buffer.add_string buf (string_of_type t);
      | Type.FunU _ | Type.TensorU _  ->
          Buffer.add_char buf '(';
          s_typeU t;
          Buffer.add_char buf ')'
      | Type.Link _ -> assert false
  in s_typeU ty;
     Buffer.contents buf

let string_of_term_const (c: term_const) : string =
  match c with
  | Cprint s -> "print(" ^ s ^ ")"
  | Cundef -> "undef"
  | Cintconst i -> Printf.sprintf "%i" i
  | Cintadd -> "intadd"
  | Cintsub -> "intsub"
  | Cintmul -> "intmul"
  | Cintdiv -> "intdiv"
  | Cinteq -> "inteq"
  | Cintslt -> "intslt"
  | Cintprint -> "intprint"

let string_of_termW (term: Term.t): string =
  let buf = Buffer.create 80 in
  let rec s_termW (t: Term.t): unit =
    match t.desc with
      | LambdaW((x, None), t1) ->
          Buffer.add_string buf "fun ";
          Buffer.add_string buf x;
          Buffer.add_string buf " -> ";
          s_termW t1
      | LambdaW((x, Some a), t1) ->
          Buffer.add_string buf "fun (";
          Buffer.add_string buf x;
          Buffer.add_string buf " : ";
          Buffer.add_string buf (string_of_type a);
          Buffer.add_string buf " ) -> ";
          s_termW t1
      | LetW(t1, (x, y, t2)) ->
          Buffer.add_string buf "let (";
          Buffer.add_string buf x;
          Buffer.add_string buf ", "; 
          Buffer.add_string buf y; 
          Buffer.add_string buf ") = "; 
          s_termW t1;
          Buffer.add_string buf " in ";
          s_termW t2
      | LetBoxW(t1, (x, t2)) ->
          Buffer.add_string buf "let [";
          Buffer.add_string buf x;
          Buffer.add_string buf "] = "; 
          s_termW t1;
          Buffer.add_string buf " in ";
          s_termW t2
      | CaseW(t1, [(x, t2); (y, t3)]) ->
          Buffer.add_string buf "case ";
          s_termW t1;
          Buffer.add_string buf " of inl(";
          Buffer.add_string buf x;
          Buffer.add_string buf ") -> ";
          s_termW t2;
          Buffer.add_string buf " | inr(";
          Buffer.add_string buf y;
          Buffer.add_string buf ") -> ";
          s_termW t3
      | CaseW(t1, l) ->
          Buffer.add_string buf "case ";
          s_termW t1;
          Buffer.add_string buf " of ";
          let n = List.length l in
          let k = ref 0 in 
          List.iter (fun (x, t) -> 
                       Buffer.add_string buf (Printf.sprintf "| in(%i, %i, %s) -> " n !k x);
                       k := !k + 1;
                       s_termW t) l
      | LoopW(t1, (x, t2)) ->
          Buffer.add_string buf "let ";
          Buffer.add_string buf x;
          Buffer.add_string buf " = ";
          s_termW t1;
          Buffer.add_string buf " loop ";
          s_termW t2
      | FoldW((alpha, a), t1) ->
          Buffer.add_string buf "fold<";
          Buffer.add_string buf (string_of_type alpha);
          Buffer.add_string buf ". ";
          Buffer.add_string buf (string_of_type a);
          Buffer.add_string buf "> ";
          s_termW t1
      | UnfoldW((alpha, a), t1) ->
          Buffer.add_string buf "unfold<";
          Buffer.add_string buf (string_of_type alpha);
          Buffer.add_string buf ". ";
          Buffer.add_string buf (string_of_type a);
          Buffer.add_string buf "> ";
          s_termW t1
      | DeleteW((alpha, a), t1) ->
          Buffer.add_string buf "delete<";
          Buffer.add_string buf (string_of_type alpha);
          Buffer.add_string buf ". ";
          Buffer.add_string buf (string_of_type a);
          Buffer.add_string buf "> ";
          s_termW t1
      | EmbedW((a, b), t1) ->
          Buffer.add_string buf "embed<";
          Buffer.add_string buf (string_of_type a);
          Buffer.add_string buf ", ";
          Buffer.add_string buf (string_of_type b);
          Buffer.add_string buf "> ";
          s_termW t1
      | ProjectW((a, b), t1) ->
          Buffer.add_string buf "project<";
          Buffer.add_string buf (string_of_type a);
          Buffer.add_string buf ", ";
          Buffer.add_string buf (string_of_type b);
          Buffer.add_string buf "> ";
          s_termW t1
      | AssignW((alpha, a), t1, t2) ->
          s_termW t1;
          Buffer.add_string buf ":=<";
          Buffer.add_string buf (string_of_type alpha);
          Buffer.add_string buf ". ";
          Buffer.add_string buf (string_of_type a);
          Buffer.add_string buf "> ";
          s_termW t2
      | _ ->
          (s_termW_app t)
  and s_termW_app (t: Term.t) =
    match t.desc with
      | AppW(t1, t2) -> 
          s_termW_app t1;
         Buffer.add_string buf " ";
         s_termW_atom t2
      | _ ->
          s_termW_atom t
  and s_termW_atom (t: Term.t) =
    match t.desc with
      | Var(x) -> 
         Buffer.add_string buf  x
      | UnitW -> 
          Buffer.add_string buf "()"
      | ConstW(s) -> 
          Buffer.add_string buf (string_of_term_const s)
      | PairW(t1, t2) -> 
          Buffer.add_char buf '(';
          s_termW t1;
          Buffer.add_string buf ", ";
          s_termW t2;
          Buffer.add_char buf ')'
      | InW(2, 0, t1) -> 
          Buffer.add_string buf "inl(";
          s_termW t1;
          Buffer.add_char buf ')'
      | InW(2, 1, t1) -> 
          Buffer.add_string buf "inr(";
          s_termW t1;
          Buffer.add_char buf ')'
      | InW(n, k, t1) ->
          Buffer.add_string buf (Printf.sprintf "in(%i, %i," n k);
          s_termW t1;
          Buffer.add_char buf ')'
      | ContW(n, k, t1) ->
          Buffer.add_string buf (Printf.sprintf "cont(%i, %i," n k);
          s_termW t1;
          Buffer.add_char buf ')'
      | TypeAnnot(t, _) ->
          s_termW_atom t
      | LambdaW(_, _) | LetW(_, _) | CaseW(_, _)
      | LoopW(_) | AppW(_, _) | FoldW _ | UnfoldW _ | DeleteW _ | AssignW _ ->
          Buffer.add_char buf '(';
          s_termW t;
          Buffer.add_char buf ')'
      | _ ->
          Buffer.add_string buf "(cannot print upper class terms yet)" 
  in s_termW term; 
     Buffer.contents buf
