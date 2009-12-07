type t

val empty : t

val is_empty : t -> bool
val is_esingleton : t -> bool
val e_choose : t -> Name.t

val to_lists : t -> Name.t list * Name.t list

val eadd :  t -> Name.t -> t
val radd :  t -> Name.t -> t
val print : t Myformat.fmt
val union : t -> t -> t
val rremove : t -> Name.t list -> t
val equal : t -> t -> bool
val rmap : (Name.t -> Name.t) -> t -> t
val lsubst : Name.t list -> t list -> t -> t
val rmem : t -> Name.t -> bool
val emem : t -> Name.t -> bool
val rfold : (Name.t -> 'a -> 'a) -> 'a -> t -> 'a
val efold : (Name.t -> 'a -> 'a) -> 'a -> t -> 'a
