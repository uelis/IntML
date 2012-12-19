(** Unification
  *
  * The unification algorithm loosely follows the
  * description in Section 1.4 of the following article:
  *   Didier Rémy. Using, Understanding, and Unraveling
  *   The OCaml Language. LNCS 2395. Springer-Verlag 2002
  *   http://pauillac.inria.fr/~remy/cours/appsem/
  *)

module type S = sig

  type tag
  type typeEq = Type.t * Type.t * (tag option)

  type failure_reason =
    | Equation_failed of typeEq
    | Cyclic_type of typeEq 

  exception Not_Unifiable of failure_reason

  val unify_pairs: typeEq list -> unit

  val unify: Type.t -> Type.t -> unit

end

module Unify(T : sig type t end) = struct

  open Type

  type tag = T.t
  type typeEq = t * t * (tag option)

  type failure_reason =
    | Equation_failed of typeEq 
    | Cyclic_type of typeEq 

  exception Not_Unifiable of failure_reason

  let rec unify_raw (c : typeEq) : unit =
    let t1, t2, tag = c in
    let c1, c2 = find t1, find t2 in
      if c1 != c2 then
        match finddesc c1, finddesc c2 with
          | Var, _ ->
              union c1 c2
          | _, Var -> 
              union c2 c1
          | NatW, NatW | ZeroW, ZeroW | OneW, OneW -> 
              ()
          | TensorW(t1, t2), TensorW(s1, s2) | FunW(t1, t2), FunW(s1, s2) 
          | BoxU(t1, t2), BoxU(s1, s2) | TensorU(t1, t2), TensorU(s1, s2) ->
              unify_raw (t1, s1 ,tag);
              unify_raw (t2, s2, tag)
          | DataW(i, ts), DataW(j, ss) when i = j -> 
              List.iter (fun (t, s) -> unify_raw (t, s, tag))
                (List.combine ts ss)
          | ContW(t1), ContW(s1) ->
              unify_raw (t1, s1 ,tag)
          | FunU(a1, t1, t2), FunU(b1, s1, s2) -> 
              unify_raw (a1, b1, tag);
              unify_raw (t1, s1, tag);
              unify_raw (t2, s2, tag)
          | _ ->
              raise (Not_Unifiable (Equation_failed c))

  let check_cycle ((t, _, _) as e : typeEq) : unit =
    let mark_open = next_mark () in
    let mark_done = next_mark () in
    let rec dfs (t: t) =
      let r = find t in
        if r.mark = mark_open then raise (Not_Unifiable(Cyclic_type(e)))
        else if (r.mark = mark_done) then ()
        else 
          begin
            r.mark <- mark_open;
            begin
              match r.desc with 
                | ContW(t1) -> dfs t1
                | TensorW(t1, t2) | FunW(t1, t2)
                | BoxU(t1, t2) | TensorU(t1, t2) -> dfs t1; dfs t2
                | FunU(t1, t2, t3) -> dfs t1; dfs t2; dfs t3
                | DataW(_, l) -> List.iter dfs l
                | _ -> ()
            end;
            r.mark <- mark_done
          end
    in dfs t

  let unify_with_cycle_check (e : typeEq) : unit =
    unify_raw e;
    check_cycle e

  let unify_pairs (eqs: typeEq list): unit =
    List.iter unify_with_cycle_check eqs

  let unify (t1 : t) (t2 : t) : unit =
    unify_with_cycle_check (t1, t2, None)

end      
