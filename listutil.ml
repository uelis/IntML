
let rec init (n : int) (f : int -> 'a) : 'a list =
   if n <= 0 then [] 
   else f 0 :: (init (n-1) (fun i -> f (i+1)))

let part n l =
  let rec part_rev n l =
    if n = 0 then ([], l) else
      let (h,t) = part_rev (n-1) l in
      match t with
        | [] -> raise Not_found
        | x::t' -> (x::h, t')
  in 
  let (h, t) = part_rev n l in
    (List.rev h, t)


