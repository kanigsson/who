type ('a,'b) t = 'a * 'b

val compare : ('a -> 'a -> int) -> ('b -> 'b -> int) ->
  ('a,'b) t -> ('a,'b) t -> int
