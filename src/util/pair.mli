type ('a,'b) t = 'a * 'b

val compare : ('a -> 'a -> int) -> ('b -> 'b -> int) ->
  ('a,'b) t -> ('a,'b) t -> int

val hash : ('a -> int) -> ('b -> int) -> ('a,'b) t -> int
val hash1 : ('a -> int) -> ('a,'a) t -> int
