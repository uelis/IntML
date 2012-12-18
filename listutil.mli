val init: int -> (int -> 'a) -> 'a list

val part: int -> 'a list -> 'a list * 'a list

val mapi: (int -> 'a -> 'b) -> 'a list -> 'b list

val iteri: (int -> 'a -> unit) -> 'a list -> unit
