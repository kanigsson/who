type t

val empty : t
val is_empty : t -> bool
val no_effvar : t -> bool

val esingleton : Name.t -> t
val is_esingleton : t -> bool
val e_choose : t -> Name.t

val rmem : t -> Name.t -> bool
val emem : t -> Name.t -> bool

val to_lists : t -> Name.t list * Name.t list
val to_rlist : t -> Name.t list 
val to_elist : t -> Name.t list 
val from_lists : Name.t list -> Name.t list -> t

val eadd :  t -> Name.t -> t
val radd :  t -> Name.t -> t
val rremove : t -> Name.t list -> t
val eremove : t -> Name.t -> t
val print : t Myformat.fmt
val print_nosep: t Myformat.fmt
val union : t -> t -> t
val equal : t -> t -> bool
val rmap : (Name.t -> Name.t) -> t -> t
val lsubst : Name.t list -> t list -> t -> t
val rfold : (Name.t -> 'a -> 'a) -> 'a -> t -> 'a
val efold : (Name.t -> 'a -> 'a) -> 'a -> t -> 'a
val eiter : (Name.t -> unit) -> t -> unit
val inter : t -> t -> t
val diff : t -> t -> t

val split : t -> t -> t * t * t
(** take two effects and return:
    * the first without the second
    * their intersection
    * the second without the first 
*)
