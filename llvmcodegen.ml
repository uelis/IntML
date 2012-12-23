open Term

let context = Llvm.global_context ()
let builder = Llvm.builder context
  
let position_at_start block builder =
  let block_begin = Llvm.instr_begin block in
    Llvm.position_builder block_begin builder

let rec log i =
  if i > 1 then 1 + (log (i - i/2)) else 0

let rec transpose l =
  let rec split_list heads tails l =
    match l with
      | [] -> List.rev heads, List.rev tails
      | [] :: _ -> assert false
      | (h :: t) :: l' -> split_list (h :: heads) (t :: tails) l' 
  in
    match l with
      | [] | [] :: _ -> []
      | _ -> 
          let heads, tails = split_list [] [] l in
            heads :: transpose tails 

let build_vector_phi (src : ((Llvm.llvalue list) * Llvm.llbasicblock) list)  
      builder
      : Llvm.llvalue list =
  let l = List.map (fun (x, src) -> List.map (fun xi -> (xi, src)) x) src in
  let l' = transpose l in
    List.map (fun isrcs -> Llvm.build_phi isrcs "z" builder) l'

module M = Map.Make(struct
                      type t = int
                      let compare = compare
                    end)

type profile = int M.t (* Invariant: nur Werte > 0 drin *)             

let print_profile p=
  let b = M.bindings p in
    List.iter (fun (i, n) -> Printf.printf "%i->%i, " i n) b;
    Printf.printf "\n"

let singleton_profile i = M.add i 1 M.empty                 

(* TODO: Definitionsbereiche klar dokumentieren! *)

(* Encapsulate bit vectors to make it easy to change the llvm-encoding. *)
module Bitvector :
sig 
  type t
  val to_profile : t -> profile

  val null : t
  val singleton : int -> Llvm.llvalue -> t

  (* concatenates all lists *)
  val pair : t -> t -> t

  (* takes the prefixes specified by profile and returns also the rest *)
  val takedrop : t -> profile -> t * t

  (* take prefix or append undefs so that value fits the profile *)
  val coerce : t -> profile -> t

  val llvalue_of_singleton : t -> Llvm.llvalue

  val build_phi: (t * Llvm.llbasicblock) list -> Llvm.llbuilder -> t
  val add_incoming: t * Llvm.llbasicblock -> t -> unit

  val packing_type: profile -> Llvm.lltype
  val pack : t -> Llvm.llvalue
  val unpack : profile -> Llvm.llvalue -> t
end = 
struct
  
  type t = { bits : (Llvm.llvalue list) M.t }

  let null = { bits = M.empty }
  let singleton i v = { bits = M.add i [v] M.empty }

  let pair v w =
    { bits = 
        M.merge (fun n vn' wn' ->
               match vn', wn' with
                 | Some vn, Some wn -> Some (vn @ wn)
                 | Some vn, None | None, Some vn -> Some vn
                 | None, None -> None)
          v.bits w.bits }

  (* precond: v enthält mindestens so viele Werte, wie vom Profil angegeben *)
  let takedrop v profile =
    { bits = M.fold (fun n ln v1 ->
              let vn = M.find n v.bits in
              let vn1, _ = Listutil.part ln vn in
              M.add n vn1 v1) profile M.empty},
    { bits = M.fold (fun n vn v2 ->
              let ln = try M.find n profile with Not_found -> 0 in
              let _, vn2 = Listutil.part ln vn in
              M.add n vn2 v2) v.bits M.empty}

  let coerce v profile =
    let rec fill_cut i l n =
      if n = 0 then [] else 
        match l with
          | [] -> Llvm.undef (Llvm.integer_type context i) :: (fill_cut i [] (n-1)) 
          | x::xs -> x :: (fill_cut i xs (n-1)) in
      { bits = 
          M.fold (fun i n v' ->
                    let vn = try M.find i v.bits with Not_found -> [] in
                      M.add i (fill_cut i vn n) v'
          ) profile M.empty }

  let llvalue_of_singleton v = 
    List.hd (snd (M.choose v.bits))

  let of_list bl = { bits = bl }

  let build_phi srcs builder =
    let sources (n : int) : ((Llvm.llvalue list) * Llvm.llbasicblock) list 
          = List.map (fun (mi, si) -> M.find n mi.bits, si) srcs in
    match srcs with
      | (src1, block1) :: rest ->
          let ns = List.map fst (M.bindings src1.bits) in
          { bits = List.fold_right (fun n map -> 
                                      M.add n (build_vector_phi (sources n) builder) map) ns M.empty }
      | [] -> assert false

  let add_incoming (y, blocky) x =
    let add_incoming_n (y, blocky) x =
      List.iter 
        (fun (yi, xi) -> Llvm.add_incoming (yi, blocky) xi)
        (List.combine y x) in
    let ns = List.map fst (M.bindings y.bits) in
      List.iter (fun n -> add_incoming_n (M.find n y.bits, blocky) (M.find n x.bits)) ns 

  let to_profile (x: t) : profile =
    M.fold (fun n xs m -> M.add n (List.length xs) m) x.bits M.empty

  let packing_type p = 
    let bndgs = M.bindings p in
    let struct_members = List.fold_right 
                 (fun (i, n) args ->
                    Array.append (Array.make n (Llvm.integer_type context i))
                      args) bndgs (Array.make 0 (Llvm.integer_type context 1)) in
    let struct_type = Llvm.packed_struct_type context struct_members in
      struct_type 

  let pack x = 
    let struct_type = packing_type (to_profile x) in
    let bndgs = M.bindings x.bits in
    let struct_content = 
      List.fold_right (fun (i, xs) vals -> xs @ vals) bndgs [] in
    let n = List.length struct_content in
    let struct_content_with_indices = 
      List.combine 
        (Listutil.init n (fun i -> i)) 
        struct_content in
      List.fold_right 
        (fun (i,v) s -> Llvm.build_insertvalue s v i "pack" builder) 
        struct_content_with_indices
        (Llvm.undef struct_type) 

  let unpack p v = 
    let pos = ref 0 in
    let rec extract n =
      if n = 0 then []
      else 
        let h = Llvm.build_extractvalue v !pos "unpack" builder in
          incr pos;
          h :: (extract (n-1))
    in
    let rec extract_bndgs b =
      match b with
        | [] -> M.empty
        | (i, n) :: rest -> 
            M.add i (extract n) (extract_bndgs rest)
    in
      { bits = extract_bndgs (M.bindings p) }
end

type encoded_value = {
  payload : Llvm.llvalue list;
  attrib: Bitvector.t
}
 (*
 * Payload:
 *   <> -> []
 *   <t1,t2> -> (payload t1) @ (payload t2)
 *   inl(t1) -> (payload t1)
 *   inr(t2) -> (payload t2)
 *
 * Attribution:
 *   <> -> []
 *   <t1,t2> -> (attrib t1) | (attrib t2)
 *   inl(t1) -> (attrib t1) | 0
 *   inl(t1) -> (attrib t1) | 1
 *
 * Payload-Size:
 *   1 -> 0
 *   N -> 1
 *   A*B -> (payload_size A) + (payload_size B)
 *   A+B -> max(payload_size A, payload_size B)
 *
 * Attrib-Size:
 *   1 -> 0
 *   N -> 0
 *   A*B -> (attrib_size A) + (attrib_size B)
 *   A+B -> max(attrib_size A, attrib_size B)
 *)

(* 
 * Namensschema: 
 * Payload: x.0, x.1, ..., x.(payload_size -1)
 * Attrib: x.a
 *)

let rec payload_size (a: Type.t) : int = 
  let payload_size_memo = Type.Typetbl.create 5 in
  let rec p_s a = 
  try Type.Typetbl.find payload_size_memo a with
    | Not_found ->
        let size =
          let open Type in
            match finddesc a with
              | Link _ -> assert false
              | ZeroW | OneW -> 0
              | Var(_) -> 1
              | NatW -> 1
              | ContW(_) -> 2
              | TensorW(a1, a2) -> p_s a1 + (p_s a2)
              | DataW(id, ps) -> 
                  if Type.Data.is_mutable id || Type.Data.is_recursive id then
                    1
                  else 
                    let cs = Type.Data.constructor_types id ps in
                      List.fold_right (fun c m -> max (p_s c) m) cs 0
              | FunW(_, _) | BoxU(_, _) | TensorU(_, _) | FunU(_, _, _) -> assert false
        in
          Type.Typetbl.add payload_size_memo a size;
          size
  in p_s a

(* aufräumen *)       
let attrib_size (a: Type.t) : profile =
  let attrib_size_memo = Type.Typetbl.create 5 in
  let rec a_s a = 
  try Type.Typetbl.find attrib_size_memo a with
    |Not_found ->
        let size =
          let open Type in
            match finddesc a with
              | Link _ -> assert false
              | Var | ZeroW | OneW | NatW | ContW _ -> M.empty
              | TensorW(a1, a2) -> M.merge (fun n x' y' -> 
                                                match x', y' with
                                                  | Some x, Some y -> Some (x+y)
                                                  | Some x, None | None, Some x -> Some x
                                                  | None, None -> None) (a_s a1) (a_s a2)
              | DataW(id, ps) -> 
                  if Type.Data.is_mutable id || Type.Data.is_recursive id then
                    M.empty
                  else
                    begin
                      let cs = Type.Data.constructor_types id ps in
                      let n = List.length cs in
                      let mx = List.fold_right (fun c mx ->
                                                  (M.merge (fun i x' y' -> 
                                                              match x', y' with
                                                                | Some x, Some y -> Some (max x y)
                                                                | Some x, None | None, Some x -> Some x
                                                                | None, None -> None) 
                                                     (a_s c) mx)) cs M.empty in
                      let i = log n in
                        if i > 0 then
                          (let ni = try M.find i mx with Not_found -> 0 in
                            M.add i (ni + 1) mx)
                        else mx
                    end
              | FunW(_, _) | BoxU(_, _) | TensorU(_, _) | FunU(_, _, _) -> assert false
        in
          Type.Typetbl.add attrib_size_memo a size;
          size
  in a_s a
       
(* TODO: check that truncation is correctly applied! 
* *)                      
let build_truncate_extend (enc : encoded_value) (a : Type.t) =
  let a_payload_size = payload_size a in
  let a_attrib_bitlen = attrib_size a in    
  let rec mk_payload p n =
    if n = 0 then [] else 
      match p with
        | [] -> Llvm.undef (Llvm.i64_type context) :: (mk_payload [] (n-1)) 
        | x::xs -> x :: (mk_payload xs (n-1)) in
  let x_payload = mk_payload enc.payload a_payload_size in
  let x_attrib = Bitvector.coerce enc.attrib a_attrib_bitlen in
    { payload = x_payload; attrib = x_attrib }

let packing_type (a: Type.t) : Llvm.lltype =
  let i64 = Llvm.i64_type context in
  let len_p = payload_size a in
  let struct_members = Array.append (Array.make len_p i64) 
                         (Array.make 1 (Bitvector.packing_type (attrib_size a))) in
  let struct_type = Llvm.packed_struct_type context struct_members in
    struct_type 

let pack_encoded_value (enc: encoded_value) (a: Type.t): Llvm.llvalue =
  let len_p = payload_size a in
  let struct_type = packing_type a in
  let struct_content = 
    (List.combine (Listutil.init len_p (fun i -> i)) enc.payload) @
    [len_p, Bitvector.pack enc.attrib] in
  let packed_enc = 
    List.fold_right 
      (fun (i,v) s -> Llvm.build_insertvalue s v i "packed" builder) 
      struct_content 
      (Llvm.undef struct_type) in
    packed_enc

let unpack_encoded_value (packed_enc: Llvm.llvalue) (a: Type.t) : encoded_value =      
  let len_p = payload_size a in
  let len_a = attrib_size a in
  let pl = Listutil.init len_p (fun i -> Llvm.build_extractvalue packed_enc i "p" builder) in
  let at = Llvm.build_extractvalue packed_enc len_p "a" builder in
    {payload = pl; attrib = Bitvector.unpack len_a at}

(* TODO: 
 * - restrict wc so that this compilation is always ok. (remove functions)
 * *)                      
let build_term 
      (the_module : Llvm.llmodule)
      (get_block: int -> Llvm.llbasicblock)
      (ctx: (var * encoded_value) list) 
      (type_ctx: (var * Type.t) list) (t: Term.t) (a: Type.t)
      : encoded_value =
  (* Add type annotations in various places *)
  let rec annotate_term (t: Term.t) : Term.t =
    match t.desc with
      | ConstW(Cundef) -> 
          let alpha = Type.newty Type.Var in
            mkTypeAnnot (mkConstW Cundef) (Some alpha)
      | Var(_) | UnitW | ConstW(_) -> t
      | TypeAnnot(t1, None) -> annotate_term t1
      | TypeAnnot(t1, Some a) -> mkTypeAnnot (annotate_term t1) (Some a)
      | PairW(t1, t2) -> 
          let alpha = Type.newty Type.Var in
            mkTypeAnnot (mkPairW (annotate_term t1) (annotate_term t2)) (Some alpha)
      | LetW(t1, (x, y, t2)) ->
          let alpha = Type.newty Type.Var in
            mkLetW (mkTypeAnnot (annotate_term t1) (Some alpha)) ((x, y), annotate_term t2)
      | InW(id, i, t1) -> 
          let alpha = Type.newty Type.Var in
            mkTypeAnnot (mkInW id i (annotate_term t1)) (Some alpha)              
      | CaseW(id, destruct, t1, cases)  ->
          let alpha = Type.newty Type.Var in
              (mkCaseW id destruct
                 (mkTypeAnnot (annotate_term t1) (Some alpha)) 
                 (List.map (fun (x, t) -> (x, annotate_term t)) cases))
      | AppW(t1, t2) -> mkAppW (annotate_term t1) (annotate_term t2)
      | LambdaW((x, a), t1) -> mkLambdaW ((x, a), annotate_term t1)
      | LoopW(t1, (x, t2)) -> 
          let alpha = Type.newty Type.Var in
            mkLoopW (annotate_term t1) (x, mkTypeAnnot (annotate_term t2) (Some alpha))
      | AssignW(id, t1, t2) -> 
          let alpha = Type.newty Type.Var in
            mkAssignW id 
              (mkTypeAnnot (annotate_term t1) (Some alpha)) 
              (annotate_term t2)
      | ContW(i, n ,t) -> 
          let alpha = Type.newty Type.Var in
            mkContW i n (mkTypeAnnot (annotate_term t) (Some alpha))
      | CallW(fn, t) ->
          let alpha = Type.newty Type.Var in
          let beta = Type.newty Type.Var in
            mkTypeAnnot 
              (mkCallW fn (mkTypeAnnot (annotate_term t) (Some alpha)))
              (Some beta)
      | LetBoxW(_, _) -> assert false 
      | HackU (_, _)|CopyU (_, _)|CaseU (_, _, _)|LetBoxU (_, _)
      | BoxTermU _| LambdaU (_, _)|AppU (_, _)|LetU (_, _)|PairU (_, _) 
      | ForceU _ | SuspendU _ | MemoU _ | ExternalU _ -> assert false
  in
  (* Compile annotated term *)
  let rec build_annotatedterm 
        (ctx: (string * encoded_value) list) 
        (t: Term.t) 
        (args: encoded_value list)
        : encoded_value =
(*    print_string (Printing.string_of_termW t);
    print_string "\n"; *)
    match t.Term.desc with
      | Var(x) -> 
          List.assoc x ctx
      | TypeAnnot({ desc = ConstW(Cundef) }, Some a) ->
          build_truncate_extend {payload = []; attrib = Bitvector.null;} a
      | ConstW(Cintconst(i)) ->
          let vali = Llvm.const_int (Llvm.i64_type context) i in
            {payload = [vali]; attrib = Bitvector.null;}
      | ConstW(Cintprint) ->
          begin
            match List.hd args with
              | {payload = [x]} -> 
                  let i8a = Llvm.pointer_type (Llvm.i8_type context) in
                  let i64 = Llvm.i64_type context in
                  let formatstr = Llvm.build_global_string "%i" "format" builder in            
                  let formatstrptr = Llvm.build_in_bounds_gep formatstr (Array.make 2 (Llvm.const_null i64)) "forrmatptr" builder in
                  let printftype = Llvm.function_type (Llvm.i64_type context) (Array.of_list [i8a; i64]) in
                  let printf = Llvm.declare_function "printf" printftype the_module in
                  let args = Array.of_list [formatstrptr; x] in
                    ignore (Llvm.build_call printf args "i" builder);
                    {payload = []; attrib = Bitvector.null }
              | _ -> assert false
          end
      | ConstW(binop) when (binop = Cintadd || binop = Cintsub || 
                            binop = Cintmul || binop = Cintdiv) ->
          begin
            match args with
              | t1enc :: t2enc :: args' ->
                  begin
                    match t1enc, t2enc with
                      | {payload = [x]},  {payload = [y]} ->
                          let res =
                            match binop with
                              | Cintadd -> Llvm.build_add x y "add" builder 
                              | Cintsub -> Llvm.build_sub x y "sub" builder 
                              | Cintmul -> Llvm.build_mul x y "mul" builder 
                              | Cintdiv -> Llvm.build_sdiv x y "sdiv" builder 
                              | _ -> assert false
                          in
                            {payload = [res]; attrib = Bitvector.null}
                      | _ -> assert false
                  end
              | _ -> assert false
          end
      | ConstW(rel) when (rel = Cinteq || rel = Cintslt) ->
          (* TODO: check *)
          begin
            match args with
              | t1enc :: t2enc :: args' ->
                  begin
                    match t1enc, t2enc with
                      | {payload = [x]; attrib = ax},  {payload = [y]; attrib = ay} ->
                          let res = 
                            match rel with
                              | Cinteq -> Llvm.build_icmp Llvm.Icmp.Ne x y "eq" builder 
                              | Cintslt -> Llvm.build_icmp Llvm.Icmp.Sge x y "slt" builder 
                              | _ -> assert false
                          in
                            {payload = []; attrib = Bitvector.singleton 1 res}
                      | _ -> assert false
                  end
              | _ -> assert false
          end
      | ConstW(Cprint(s)) ->
          let i64 = Llvm.i64_type context in
          let str = Llvm.build_global_string s "s" builder in            
          let strptr = Llvm.build_in_bounds_gep str (Array.make 2 (Llvm.const_null i64)) "strptr" builder in
          let strptrint = Llvm.build_ptrtoint strptr i64 "strptrint" builder in
            (* declare puts *)
          let i8a = Llvm.pointer_type (Llvm.i8_type context) in
          let formatstr = Llvm.build_global_string "%s" "format" builder in
          let formatstrptr = Llvm.build_in_bounds_gep formatstr (Array.make 2 (Llvm.const_null i64)) "forrmatptr" builder in
          let printftype = Llvm.function_type (Llvm.i64_type context) (Array.of_list [i8a; i64]) in
          let printf = Llvm.declare_function "printf" printftype the_module in
          let args = Array.of_list [formatstrptr; strptrint] in
            ignore (Llvm.build_call printf args "i" builder);
(*          let i8a = Llvm.pointer_type (Llvm.i8_type context) in
          let putstype = Llvm.function_type (Llvm.i64_type context) (Array.make 1 i8a) in
          let puts = Llvm.declare_function "puts" putstype the_module in
          let args = Array.make 1 strptr in
            ignore (Llvm.build_call puts args "i" builder);*)
            {payload = []; attrib = Bitvector.null}
      | UnitW ->
          {payload = []; attrib = Bitvector.null}
      | TypeAnnot({ desc = PairW(t1, t2) }, Some a) ->
          assert (args = []);
          begin
            match Type.finddesc a with
              | Type.TensorW(a1, a2) ->
                  let t1enc = build_annotatedterm ctx t1 [] in
                  let t2enc = build_annotatedterm ctx t2 [] in
                  let ta = Bitvector.pair t1enc.attrib t2enc.attrib in
                    {payload = t1enc.payload @ t2enc.payload; attrib = ta}
              | _ -> assert false
          end
      | LetW({ desc = TypeAnnot(s, Some a) }, (x, y, t)) ->
          begin
            match Type.finddesc a with
              | Type.TensorW(ax, ay) ->
                  let senc = build_annotatedterm ctx s [] in
                  let len_sxp = payload_size ax in
                  let len_syp = payload_size ay in
                  let len_sxa = attrib_size ax in
(*                  let len_sya = attrib_size ay in*)
                    assert (List.length senc.payload = len_sxp + len_syp);
                    let sxp, syp = Listutil.part len_sxp senc.payload in
                    let sxa, sya = Bitvector.takedrop senc.attrib len_sxa in
                     (* assert (Bitvector.length sya = len_sya); *)
                      build_annotatedterm ((x, {payload = sxp; attrib = sxa }) :: 
                                           (y, {payload = syp; attrib = sya }) :: ctx) t args
              | _ -> assert false
          end
      | TypeAnnot({ desc = InW(id, i, t) }, Some a) 
          when (Type.Data.constructor_count id = 1) && 
               (not (Type.Data.is_mutable id || Type.Data.is_recursive id)) ->
          let tenc = build_annotatedterm ctx t [] in
            build_truncate_extend tenc a
      | TypeAnnot({ desc = InW(id, i, t) }, Some a) ->
          assert (args = []);
          let n = Type.Data.constructor_count id in
          let tenc = build_annotatedterm ctx t [] in
          let branch = Llvm.const_int (Llvm.integer_type context (log n)) i in
          let attrib_branch = Bitvector.pair (Bitvector.singleton (log n) branch) tenc.attrib in
          let denc = { payload = tenc.payload; attrib = attrib_branch} in
          if Type.Data.is_mutable id || Type.Data.is_recursive id then
            let i64 = Llvm.i64_type context in
            let malloctype = Llvm.function_type 
                               (Llvm.pointer_type (Llvm.i8_type context)) 
                               (Array.of_list [i64]) in
            let malloc = Llvm.declare_function "malloc" malloctype the_module in
            let cs_types = 
              match Type.finddesc a with
                | Type.DataW(id, ps) -> Type.Data.constructor_types id ps 
                | _ -> assert false in
            let a_unfolded = Type.newty (Type.DataW(Type.Data.sumid n, cs_types)) in
            let a_struct = packing_type a_unfolded in
            let denc_packed = pack_encoded_value (build_truncate_extend denc a_unfolded) a_unfolded in
            let mem_i8ptr = Llvm.build_call malloc (Array.of_list [Llvm.size_of a_struct]) 
                              "memi8" builder in
            let mem_a_struct_ptr = Llvm.build_bitcast mem_i8ptr (Llvm.pointer_type a_struct) 
                                     "memstruct" builder in
              ignore (Llvm.build_store denc_packed mem_a_struct_ptr builder);
              let pl = Llvm.build_ptrtoint mem_a_struct_ptr i64 "memint" builder in
                {payload = [pl]; attrib = Bitvector.null}
          else 
              build_truncate_extend denc a 
      | CaseW(id, destruct, { desc = TypeAnnot(u, Some a) }, cases) ->           
          let n = List.length cases in
          assert (n > 0);
          let cs_types = 
            match Type.finddesc a with
              | Type.DataW(id, ps) -> Type.Data.constructor_types id ps 
              | _ -> assert false in
          let uenc = 
            if Type.Data.is_mutable id || Type.Data.is_recursive id then
              begin
                let a_unfolded = Type.newty (Type.DataW(Type.Data.sumid n, cs_types)) in
                let a_struct = packing_type a_unfolded in
                  match build_annotatedterm ctx u args with
                    | {payload = [tptrint] } ->
                        let tptr = Llvm.build_inttoptr tptrint (Llvm.pointer_type a_struct) "tptr" builder in
                        let tstruct = Llvm.build_load tptr "tstruct" builder in
                          if destruct then
                            begin
                              let i64 = Llvm.i64_type context in
                              let freetype = Llvm.function_type (Llvm.void_type context) (Array.of_list [i64]) in
                              let free = Llvm.declare_function "free" freetype the_module in
                                ignore (Llvm.build_call free (Array.of_list [tptrint]) "" builder)
                            end;
                          unpack_encoded_value tstruct a_unfolded
                    | _ -> assert false
              end
            else    
              build_annotatedterm ctx u [] in
            begin
              match cases with
                | [(x, t)] ->
                    build_annotatedterm ((x, uenc) :: ctx) t [] 
              | _ ->
              begin
(*          assert (Bitvector.length uenc.attrib > 0); *)
                let cond, xya = Bitvector.takedrop uenc.attrib (singleton_profile (log n)) in
                let xyenc = {payload = uenc.payload; attrib = xya } in
                let encs = List.map (fun ((x, s), c) -> ((x, build_truncate_extend xyenc c), s))
                             (List.combine cases cs_types) in
                let func = Llvm.block_parent (Llvm.insertion_block builder) in
                let blocks = Listutil.init n (fun i -> 
                                                Llvm.append_block context 
                                                  ("case" ^ (string_of_int i)) func) in 
                let res_block = Llvm.append_block context "case_res" func in
                let default_block = List.hd blocks in 
                let cond' = Bitvector.llvalue_of_singleton cond in
                let switch = Llvm.build_switch cond' default_block (n-1) builder in
                (* build cases *)
                let results = 
                  Listutil.mapi 
                    (fun i (block, ((x, xenc), s)) -> 
                       if i > 0 then
                         Llvm.add_case switch 
                           (Llvm.const_int (Llvm.integer_type context (log n)) i)
                           block;
                       Llvm.position_at_end block builder;
                       let senc = build_annotatedterm ((x, xenc) :: ctx) s args in
                       let _ = Llvm.build_br res_block builder in
                       let block' = Llvm.insertion_block builder in
                         senc, block'
                    ) (List.combine blocks encs) in
                  (* build phi *)
                  Llvm.position_at_end res_block builder;
                  let z_attrib = Bitvector.build_phi 
                                   (List.map (fun (senc, block) -> senc.attrib, block) 
                                      results)
                                   builder in
                  let z_payload = build_vector_phi  
                                    (List.map (fun (senc, block) -> senc.payload, block) 
                                       results)
                                    builder in
                    {payload = z_payload; attrib = z_attrib}
              end
            end
      | LoopW(u, (x, { desc = TypeAnnot(t, Some a) })) -> 
          let ax, ay = 
            match Type.finddesc a with
              | Type.DataW(id, [ax; ay]) when id = Type.Data.sumid 2 -> ax, ay
              | _ -> assert false in
          let uenc = build_annotatedterm ctx u [] in
          let block_init = Llvm.insertion_block builder in                             
          let func = Llvm.block_parent (Llvm.insertion_block builder) in
          let block_loop = Llvm.append_block context "loop" func in 
            let _ = Llvm.build_br block_loop builder in
            Llvm.position_at_end block_loop builder;
          let z_payload = 
            List.map (fun x -> Llvm.build_phi [(x, block_init)] "z" builder)
              uenc.payload in
          let z_attrib = Bitvector.build_phi [(uenc.attrib, block_init)] builder in
          let xenc = { payload = z_payload; attrib = z_attrib } in
          let tenc = build_annotatedterm ((x, xenc) :: ctx) t [] (* TODO *) in 
(*          assert (Bitvector.length tenc.attrib > 0); *)
          let cond, xya = Bitvector.takedrop tenc.attrib (singleton_profile 1) in
          let xyenc = {payload = tenc.payload; attrib = xya } in
          let xenc = build_truncate_extend xyenc ax in
          let yenc = build_truncate_extend xyenc ay in
          let block_res = Llvm.append_block context "case_res" func in
          let cond' = Bitvector.llvalue_of_singleton cond in
            ignore (Llvm.build_cond_br cond' block_loop block_res builder);
            let block_curr = Llvm.insertion_block builder in 
            List.iter (fun (y, phinode) ->
                         Llvm.add_incoming (y, block_curr) phinode)
              (List.combine yenc.payload z_payload);
            Bitvector.add_incoming (yenc.attrib, block_curr) z_attrib;
            Llvm.position_at_end block_res builder;
              xenc
      | AssignW(id, {desc= TypeAnnot(s, Some a)}, t) ->
          assert (Type.Data.is_mutable id);
          let senc = build_annotatedterm ctx s args in
          let tenc = build_annotatedterm ctx t args in
          let cs_types = 
            match Type.finddesc a with
              | Type.DataW(id, ps) -> Type.Data.constructor_types id ps 
              | _ -> assert false in
          let n = List.length cs_types in
          let a_unfolded = Type.newty (Type.DataW(Type.Data.sumid n, cs_types)) in
          let a_struct = packing_type a_unfolded in
            begin
              match senc, tenc with
                | {payload = [sptrint] }, {payload = [tptrint]} ->
                    let sptr = Llvm.build_inttoptr sptrint (Llvm.pointer_type a_struct) "sptr" builder in
                    let tptr = Llvm.build_inttoptr tptrint (Llvm.pointer_type a_struct) "sptr" builder in
                    let tstruct = Llvm.build_load tptr "tstruct" builder in
                      ignore (Llvm.build_store tstruct sptr builder);
                      {payload = []; attrib = Bitvector.null}
                | _ -> assert false
            end
      | ContW(i, _, { desc = TypeAnnot(t, Some a) }) ->
          let i64 = Llvm.i64_type context in
          let block = get_block i in
          let func = Llvm.block_parent (Llvm.insertion_block builder) in
          let dst_address_ptr = Llvm.block_address func block in
          let dst_address = Llvm.build_ptrtoint dst_address_ptr i64 "blockaddr" builder in
          let tenc = build_annotatedterm ctx t args in
          let a_struct = packing_type a in
          let tenc_packed = pack_encoded_value tenc a in
          (* store contenc_packed in memory and return pointer *)
          let malloctype = Llvm.function_type 
                             (Llvm.pointer_type (Llvm.i8_type context)) 
                             (Array.of_list [i64]) in
          let malloc = Llvm.declare_function "malloc" malloctype the_module in
          let mem_i8ptr = Llvm.build_call malloc (Array.of_list [Llvm.size_of a_struct]) 
                            "memi8" builder in
          let mem_a_struct_ptr = Llvm.build_bitcast mem_i8ptr (Llvm.pointer_type a_struct) 
                                   "memstruct" builder in
          ignore (Llvm.build_store tenc_packed mem_a_struct_ptr builder);
          let pl = Llvm.build_ptrtoint mem_a_struct_ptr i64 "memint" builder in
            {payload = [dst_address; pl]; attrib = Bitvector.null}
      | TypeAnnot({ desc = CallW(fn, { desc = TypeAnnot(t, Some argty) }) }, Some resty) ->
          let arg_struct = packing_type argty in
          let res_struct = packing_type resty in
          let ftype = Llvm.function_type res_struct  (Array.of_list [arg_struct]) in
          let f = Llvm.declare_function ("IntML" ^ fn) ftype the_module in
          let tenc = build_annotatedterm ctx t args in
          let tenc_packed = pack_encoded_value tenc argty in
          let res_packed = Llvm.build_call f (Array.of_list [tenc_packed]) 
                             "res" builder in
            unpack_encoded_value res_packed resty
      | TypeAnnot(t, _) ->
          build_annotatedterm ctx t args
      | AppW(t1, t2) ->
          let t2enc = build_annotatedterm ctx t2 [] in
            build_annotatedterm ctx t1 (t2enc :: args)
      | LambdaW((x, a), t1) ->
          (match args with
             | [] -> failwith (Printf.sprintf "all functions must be fully applied %s" (Printing.string_of_termW t))
             | t2enc :: args' ->
                 build_annotatedterm ((x, t2enc) :: ctx) t1 args')
      | _ -> 
          Printf.printf "%s\n" (Printing.string_of_termW t);
          failwith "TODO_llvm"
  in
  let t_annotated = mkTypeAnnot (freshen_type_vars (annotate_term t)) (Some a) in
  let _ = Typing.principal_typeW type_ctx t_annotated in    
    build_annotatedterm ctx t_annotated []

let unpack_cont_dest (e : encoded_value) : Llvm.llvalue =
  match e with
    | {payload = dst_addr :: ptr :: _ } ->
        Llvm.build_inttoptr dst_addr (Llvm.pointer_type (Llvm.i8_type context)) "dstptr" builder
    | _ -> assert false

let unpack_cont_message (e : encoded_value) (a: Type.t) : encoded_value =
  let sigma_type, v_type = 
    match Type.finddesc a with
      | Type.TensorW(sigma, v) -> sigma, v
      | _ -> assert false in
  let sigma_type_struct = packing_type sigma_type in
  match e with
    | {payload = _ :: ptr :: message ; attrib = attr } ->
        let addrptr = Llvm.build_inttoptr ptr (Llvm.pointer_type sigma_type_struct) "addrptr" builder in
        let destsigma_packed = Llvm.build_load addrptr "sigmapacked" builder in
        let sigma = unpack_encoded_value destsigma_packed sigma_type in
        let v = { payload = message; attrib = attr } in
          (* (does nothing in all cases except those that can't actually happen;
           *  these cases could also be omitted) *)
          { payload = sigma.payload @ v.payload; 
            attrib = Bitvector.pair sigma.attrib v.attrib }
    | _ -> assert false


let build_ssa_blocks (the_module : Llvm.llmodule) (func : Llvm.llvalue) 
      (ssa_func : Ssa.func) : unit =
  let blocks = Hashtbl.create 10 in
  let phi_nodes = Hashtbl.create 10 in    
  let get_block name =
    try
      Hashtbl.find blocks name
    with Not_found ->
      let label = Printf.sprintf "L%i" name in
      let block = Llvm.append_block context label func in
        Hashtbl.add blocks name block;
        block in
  let connect_to src_block encoded_value dst =
    try 
      let phi = Hashtbl.find phi_nodes dst in
        List.iter 
          (fun (phix, x) -> Llvm.add_incoming (x, src_block) phix)
          (List.combine phi.payload encoded_value.payload);
        Bitvector.add_incoming (encoded_value.attrib, src_block) phi.attrib
        (* add (encoded_value, source) to phi node *)
    with Not_found ->
      (* TODO: Bei Grad 1 braucht man keine Phi-Knoten *)
      begin
        position_at_start (get_block dst) builder;
        let payload = List.map (fun x -> Llvm.build_phi [(x, src_block)] "g" builder) encoded_value.payload in
        let attrib = Bitvector.build_phi [(encoded_value.attrib, src_block)] builder in
        let phi = { payload = payload; attrib = attrib } in
          Hashtbl.add phi_nodes dst phi
      end
      (* add new phi node with (encoded_value, source) to block dst *)
  in
  (* TODO: share *)
  let dynamic_dest_blocks = Hashtbl.create 10 in
  let dynamic_phi_nodes = Hashtbl.create 10 in    
  let get_dynamic_dest_block name =
    try
      Hashtbl.find dynamic_dest_blocks name
    with Not_found ->
      let label = Printf.sprintf "D%i" name in
      let block = Llvm.append_block context label func in
        Hashtbl.add dynamic_dest_blocks name block;
        block in
  let dynamic_connect_to src_block encoded_value dst =
    try 
      let phi = Hashtbl.find dynamic_phi_nodes dst in
        List.iter 
          (fun (phix, x) -> Llvm.add_incoming (x, src_block) phix)
          (List.combine phi.payload encoded_value.payload);
        Bitvector.add_incoming (encoded_value.attrib, src_block) phi.attrib
        (* add (encoded_value, source) to phi node *)
    with Not_found ->
      (* TODO: Bei Grad 1 braucht man keine Phi-Knoten *)
      begin
        position_at_start (get_dynamic_dest_block dst) builder;
        let payload = List.map (fun x -> Llvm.build_phi [(x, src_block)] "g" builder) encoded_value.payload in
        let attrib = Bitvector.build_phi [(encoded_value.attrib, src_block)] builder in
        let phi = { payload = payload; attrib = attrib } in
          Hashtbl.add dynamic_phi_nodes dst phi
      end
      (* add new phi node with (encoded_value, source) to block dst *)
  in
  let dynamic_built = Hashtbl.create 10 in
  let build_coercion_block dst =
    if not (Hashtbl.mem dynamic_built dst.Ssa.name) then
      begin
        Hashtbl.add dynamic_built dst.Ssa.name true;
        let d_block = get_dynamic_dest_block dst.Ssa.name in
          Llvm.position_at_end d_block builder;
          let ev = Hashtbl.find dynamic_phi_nodes dst.Ssa.name in
          let v = unpack_cont_message ev dst.Ssa.message_type in
            ignore (Llvm.build_br (get_block dst.Ssa.name) builder);
            connect_to d_block v dst.Ssa.name
      end in
  let rec mkLets lets t =
    match lets with
      | [] -> t
      | (s, (x, y)) :: lets' -> mkLets lets' (mkLetW s ((x, y), t)) 
  in
    (* make entry block *)
  let entry_block = Llvm.append_block context "entry" func in
    let packed_arg = Llvm.param func 0 in      
    Llvm.set_value_name "packed_arg" packed_arg;
    Llvm.position_at_end entry_block builder;
    let arg = unpack_encoded_value packed_arg ssa_func.Ssa.argument_type in
    ignore (Llvm.build_br (get_block ssa_func.Ssa.entry_block) builder);
    connect_to entry_block arg ssa_func.Ssa.entry_block;
    (* build unconnected blocks *)
    let open Ssa in
    List.iter 
      (fun block ->
         match block with
           | Unreachable(src) -> 
               (*                       Printf.printf "%i --> \n" src.name; *)
               Llvm.position_at_end (get_block src.name) builder;
               let senc = Hashtbl.find phi_nodes src.name in
                 ignore (Llvm.build_br (get_block src.name) builder);
                 connect_to (get_block src.name) senc src.name
           | Direct(src, x, lets, body, dst) ->
               Llvm.position_at_end (get_block src.name) builder;
               let senc = Hashtbl.find phi_nodes src.name in
               let lets', t = Ssa.reduce (mkLets lets body) in
               let ev = build_term the_module get_dynamic_dest_block
                          [(x, senc)] [(x, src.message_type)] (mkLets lets' t) dst.message_type in
               let src_block = Llvm.insertion_block builder in
                 ignore (Llvm.build_br (get_block dst.name) builder);
                 connect_to src_block ev dst.name
           | InDirect(src, x, lets, body, dsts) ->
               Llvm.position_at_end (get_block src.name) builder;
               let senc = Hashtbl.find phi_nodes src.name in
               let lets', t = Ssa.reduce (mkLets lets body) in
               let alpha = Type.newty Type.Var in
               let contalpha = Type.newty (Type.ContW alpha) in
               let message_type = Type.newty Type.Var in
               let ev = build_term the_module get_dynamic_dest_block
                          [(x, senc)] [(x, src.message_type)] (mkLets lets' t) 
                          (Type.newty (Type.TensorW(contalpha, message_type))) in
               let dst = unpack_cont_dest ev in
               let src_block = Llvm.insertion_block builder in
               let branch = Llvm.build_indirect_br dst (List.length dsts) builder in
                 List.iter (fun dst ->
                              Llvm.add_destination branch (get_dynamic_dest_block dst.name);
                              let v_type = 
                                match Type.finddesc dst.message_type with
                                  | Type.TensorW(sigma, v) -> v
                                  | _ -> assert false in
                              let v = build_truncate_extend ev
                                        (Type.newty (Type.TensorW(contalpha, v_type))) in
                              dynamic_connect_to src_block v dst.name;
                              build_coercion_block dst
                 ) dsts
           | Branch(src, x, lets, (id, s, cases)) (* (xl, bodyl, dst1), (xr, bodyr, dst2)) *) ->
               begin
                 let n = List.length cases in
                 assert (n > 1);
                 let params = List.map (fun (x, b, dst) -> dst.message_type) cases in
                 let sumid = Type.Data.sumid n in
                 let sum = Type.newty (Type.DataW(Type.Data.sumid n, params)) in
                 let lets', t = 
                   reduce (mkLets lets (mkCaseW id false s 
                                          (Listutil.mapi 
                                             (fun i (x, body, _) -> (x, mkInW sumid i body))
                                             cases
                                          ))) in
                 let src_block = get_block src.name in
                   Llvm.position_at_end src_block builder;
                   let senc = Hashtbl.find phi_nodes src.name in
                   let tenc = build_term the_module get_dynamic_dest_block
                                [(x, senc)] [(x, src.message_type)] (mkLets lets' t)
                                sum in
                   let cond, da = Bitvector.takedrop tenc.attrib (singleton_profile (log n))in
                   let denc_all = { payload = tenc.payload; attrib = da } in
                   let dencs = List.map (fun (x, b, dst) -> build_truncate_extend denc_all dst.message_type) cases in
                   let dsts = List.map (fun (x, b, dst) -> dst) cases in
                   let cond' = Bitvector.llvalue_of_singleton cond in
                   let src_block = Llvm.insertion_block builder in
                   let default_block = get_block (List.hd dsts).name in
                   let switch = Llvm.build_switch cond' default_block (List.length dencs - 1) builder in
                     Listutil.iteri (fun i dst -> 
                                       if i > 0 then (* first case is default *)
                                         Llvm.add_case switch 
                                         (Llvm.const_int (Llvm.integer_type context (log n)) i)
                                         (get_block dst.name)) dsts;
                     List.iter (fun (denc, dst) -> 
                                  connect_to src_block denc dst.name)
                       (List.combine dencs dsts)
               end 
           | Return(src, x, lets, body, return_type) ->
               Llvm.position_at_end (get_block src.name) builder;
               let senc = Hashtbl.find phi_nodes src.name in
               let lets', t = Ssa.reduce (mkLets lets body) in
               let ev = build_term the_module get_dynamic_dest_block
                          [(x, senc)] [(x, src.message_type)] (mkLets lets' t) return_type in
(*               let pty = packing_type return_type in*)
               let pev = pack_encoded_value ev return_type in
                 ignore (Llvm.build_ret pev builder)
                   (* TODO: actual return *)
      )                         
      ssa_func.blocks


(* Must be applied to circuit of type [A] *)    
let llvm_compile (ssa_func : Ssa.func) : Llvm.llmodule = 
  let the_module = Llvm.create_module context "intml" in
(*  let ssa_func = Ssa.trace c in *)
  let arg_ty = packing_type ssa_func.Ssa.argument_type in
  let ret_ty = packing_type ssa_func.Ssa.return_type in
  let ft = Llvm.function_type ret_ty (Array.make 1 arg_ty) in
  let func = Llvm.declare_function ("IntML" ^ ssa_func.Ssa.func_name) ft the_module in
    build_ssa_blocks the_module func ssa_func;
    (* make main function *)
    if ssa_func.Ssa.func_name = "main" then
      begin
        let void_ty = Llvm.void_type context in
        let main_ty = Llvm.function_type void_ty (Array.make 0 void_ty) in
        let main = Llvm.declare_function "main" main_ty the_module in
        let start_block = Llvm.append_block context "start" main in 
        let args = Array.of_list [Llvm.undef arg_ty] in
          Llvm.position_at_end start_block builder;
          ignore (Llvm.build_call func args "ret" builder);
          ignore (Llvm.build_ret_void builder)
      end;
(*    Llvm.dump_module the_module; *)
    the_module
