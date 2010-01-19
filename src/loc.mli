type loc = {st: int * int; en: int * int}
type 'a t = { info:loc ; c : 'a }

val dummy : loc
val mk : loc -> 'a -> 'a t

val strip_info : 'a t list -> 'a list
val embrace : loc -> loc -> loc
