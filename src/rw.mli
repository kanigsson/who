type t

val equal : t -> t -> bool
val empty : t
val is_empty : t -> bool

val reads : t -> Effect.t
val writes : t -> Effect.t
val reads_only : t -> Effect.t
val read_write : t -> Effect.t * Effect.t

val mk : read:Effect.t -> write:Effect.t -> t
val map : (Effect.t -> Effect.t) -> t -> t

val union : t -> t -> t
val union3 : t -> t -> t -> t
val rremove : t -> Name.t list -> t


val overapprox : t -> Effect.t
val kernel : t -> Effect.t

module Convert : sig
  val t : Name.Env.t -> t -> PrintTree.rw
end

val print : t Myformat.fmt