type 'a t = 'a list
type 'a eq = 'a -> 'a -> bool

val equal : 'a eq -> 'a t -> 'a t -> bool
val mem : 'a eq -> 'a -> 'a t -> bool


val union : 'a eq -> 'a t -> 'a t -> 'a t
val equal_unsorted : 'a eq -> 'a t -> 'a t -> bool

val fold_map : ('a  -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list

val hash : ('a -> int) -> int -> 'a list -> int
