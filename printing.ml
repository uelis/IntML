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
    (* TODO: this is awkward *)
  let cycles = Hashtbl.create 10  in
  let check_cycle (t : Type.t) : unit =
    let mark_open = Type.next_mark () in
    let mark_done = Type.next_mark () in
    let rec dfs (t: Type.t) =
      let r = Type.find t in
        if r.Type.mark = mark_open then 
          Hashtbl.add cycles r.Type.id None
        else if (r.Type.mark = mark_done) then ()
        else 
          begin
            r.Type.mark <- mark_open;
            begin
              match r.Type.desc with 
                | Type.ContW(t1) -> dfs t1
                | Type.TensorW(t1, t2) | Type.FunW(t1, t2)
                | Type.BoxU(t1, t2) | Type.TensorU(t1, t2) -> dfs t1; dfs t2
                | Type.FunU(t1, t2, t3) -> dfs t1; dfs t2; dfs t3
                | Type.DataW(_, l) -> List.iter dfs l
                | _ -> ()
            end;
            r.Type.mark <- mark_done
          end
    in 
      dfs t in
    check_cycle ty;
  let rec check_rec t = 
    let r = Type.find t in
      try
        match Hashtbl.find cycles r.Type.id with
          | None -> 
              let x = name_of_typevar (Type.newty Type.Var) in
                Hashtbl.replace cycles r.Type.id (Some x);
                Buffer.add_string buf ("(rec '" ^ x ^ ". ");
                s_typeW ~subcase:true r;
                Buffer.add_string buf ")";
                false
          | Some x ->
              Buffer.add_string buf ("'" ^ x); 
              false
      with Not_found -> true 
  and s_typeW ?subcase:(subcase=false) (t: Type.t) =
    if subcase || (check_rec t) then 
    match (Type.finddesc t) with
      | Type.FunW(t1, t2) ->
          s_typeW_summand t1;
          Buffer.add_string buf " -> ";
            s_typeW t2 
      | _ -> 
          s_typeW_summand ~subcase:true t
  and s_typeW_summand ?subcase:(subcase=false) (t: Type.t) =
    if subcase || (check_rec t) then 
    match (Type.finddesc t) with
      | Type.DataW(id, [t1; t2]) when id = Type.Data.sumid 2 ->
            s_typeW_summand t1; 
          Buffer.add_string buf " + ";
          s_typeW_factor t2
      | Type.DataW(id, []) when id = Type.Data.sumid 0 ->
          Buffer.add_string buf "0"
      | Type.DataW(id, [])  ->
          Buffer.add_string buf id
      | Type.DataW(id, t1 :: l) ->
          Buffer.add_string buf id;
          Buffer.add_string buf "<";
            s_typeW_summand t1;
          List.iter (fun t2 -> Buffer.add_string buf ", ";
                               s_typeW_summand t2) l;
          Buffer.add_string buf ">";
      | _ -> 
          s_typeW_factor ~subcase:true t
  and s_typeW_factor ?subcase:(subcase=false) (t: Type.t) =
    if subcase || (check_rec t) then 
    match (Type.finddesc t) with
      | Type.TensorW(t1, t2) ->
            s_typeW_factor t1;
          Buffer.add_string buf " * ";
          s_typeW_atom t2
      | _ -> 
          s_typeW_atom ~subcase:true t
  and s_typeW_atom ?subcase:(subcase=false) (t: Type.t) =
    if subcase || (check_rec t) then 
    match (Type.finddesc t) with
      | Type.Var ->  
          Buffer.add_char buf '\'';
          Buffer.add_string buf (name_of_typevar t)
      | Type.NatW -> Buffer.add_string buf "int"
      | Type.ZeroW -> Buffer.add_char buf '0'
      | Type.OneW -> Buffer.add_string buf "unit"
      | Type.ContW(ret) ->
          Buffer.add_string buf "cont<";
            s_typeW ret;
          Buffer.add_char buf '>'
      | Type.FunW _ | Type.DataW _ | Type.TensorW _ ->
          Buffer.add_char buf '(';
            s_typeW t;
          Buffer.add_char buf ')';
      | Type.FunU _ | Type.TensorU _ | Type.BoxU _ ->
          s_typeU ~subcase:true t
      | Type.Link _ -> assert false
  and s_typeU ?subcase:(subcase=false) (t: Type.t) =
    if subcase || (check_rec t) then 
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
          s_typeU_factor ~subcase:true t
  and s_typeU_factor ?subcase:(subcase=false) (t: Type.t) =
    if subcase || (check_rec t) then 
    match (Type.finddesc t) with
      | Type.TensorU(t1, t2) ->
            s_typeU_factor t1;
          Buffer.add_string buf " * ";
          s_typeU_atom t2
      | _ -> 
          s_typeU_atom ~subcase:true t
  and s_typeU_atom ?subcase:(subcase=false) (t: Type.t) =
    if subcase || (check_rec t) then 
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
      | Type.DataW _ | Type.TensorW _ | Type.ContW _ ->
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
      | Type.DataW _ | Type.TensorW _ | Type.ContW _ ->
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
      | CaseW(id, destruct, t1, l) ->
          Buffer.add_string buf "case ";
          s_termW t1;
          Buffer.add_string buf " of ";
          let k = ref 0 in 
          List.iter (fun (x, t) -> 
                       let conname = List.nth (Type.Data.constructor_names id) !k in
                       if !k > 0 then Buffer.add_string buf " | "; 
                       Buffer.add_string buf (Printf.sprintf "%s(%s) -> " conname x);
                       k := !k + 1;
                       s_termW t) l
      | LoopW(t1, (x, t2)) ->
          Buffer.add_string buf "let ";
          Buffer.add_string buf x;
          Buffer.add_string buf " = ";
          s_termW t1;
          Buffer.add_string buf " loop ";
          s_termW t2
      | InW(id, k, t1) ->
          let cname = List.nth (Type.Data.constructor_names id) k in
          Buffer.add_string buf cname;
          Buffer.add_string buf " ";
          s_termW_atom t1
      | AssignW(id, t1, t2) ->
          s_termW t1;
          Buffer.add_string buf ":=<";
          Buffer.add_string buf id;
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
      | ContW(n, k, t1) ->
          Buffer.add_string buf (Printf.sprintf "cont(%i, %i, " n k);
          s_termW t1;
          Buffer.add_char buf ')'
      | CallW(fn, t1) ->
          Buffer.add_string buf (Printf.sprintf "call(%s, " fn);
          s_termW t1;
          Buffer.add_char buf ')'
      | TypeAnnot(t, _) ->
          s_termW_atom t
      | LambdaW(_, _) | LetW(_, _) | CaseW _ | InW _ 
      | LoopW(_) | AppW(_, _) | AssignW _ ->
          Buffer.add_char buf '(';
          s_termW t;
          Buffer.add_char buf ')'
      | _ ->
          Buffer.add_string buf "(cannot print upper class terms yet)" 
  in s_termW term; 
     Buffer.contents buf

let string_of_data id =
  let buf = Buffer.create 80 in
  let name = id in
  let cnames = Type.Data.constructor_names id in
  let nparams = Type.Data.params id in
  let params = Listutil.init nparams (fun x -> Type.newty Type.Var) in
  let ctypes = Type.Data.constructor_types id params in
  let cs = List.combine cnames ctypes in
    Buffer.add_string buf "type ";
    Buffer.add_string buf name;
    if (nparams > 0) then begin
      Buffer.add_string buf "<";
      Buffer.add_string buf (String.concat "," (List.map string_of_type params));
      Buffer.add_string buf ">";
    end;
    Buffer.add_string buf " = ";
    Buffer.add_string buf 
      (String.concat " | " 
         (List.map (fun (n, t) -> 
                      Printf.sprintf "%s of %s" n (string_of_type t)) cs));
    Buffer.contents buf


