type t = Effect.t * Effect.t

val equal : t -> t -> bool
val empty : t
val is_empty : t -> bool

val union : t -> t -> t
val union3 : t -> t -> t -> t
val rremove : t -> Name.t list -> t

val overapprox : t -> Effect.t

module Convert : sig
  val t : Name.Env.t -> t -> PrintTree.rw
end

val print : t Myformat.fmt
