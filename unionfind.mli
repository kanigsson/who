type 'a t

val fresh : 'a -> 'a t

val find : 'a t -> 'a t
val desc : 'a t -> 'a
val tag : 'a t -> int
val union : ('a -> 'a -> 'a) -> 'a t -> 'a t -> unit
val equal : 'a t -> 'a t -> bool
