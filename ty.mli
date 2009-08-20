type ('a,'b,'c) t' = 
  | Var of Name.t
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c
  | PureArr of 'a * 'a
  | App of Name.t * ('a,'b,'c) Inst.t
  | Ref of 'b * 'a
  | Map of 'c
type t = C of (t,Name.t,NEffect.t) t'

val print : t Myformat.fmt
val print_list : unit Myformat.fmt -> t list Myformat.fmt
val print' : 'a Myformat.fmt -> 'b Myformat.fmt -> 'c Myformat.fmt -> 
              ('a -> bool) -> (('a ,'b,'c) t') Myformat.fmt

val is_compound : ('a,'b,'c) t' -> bool
val var : Name.t -> t
val const : Const.ty -> t
val arrow : t -> t -> NEffect.t -> t
val caparrow : t -> t -> NEffect.t -> Name.t list -> t
val parr : t -> t -> t
val tuple : t -> t -> t
val ref_ : Name.t -> t -> t
val map : NEffect.t -> t
val unit : t
val prop : t
val bool : t
val int : t

val arg : t -> t
val result : t -> t
val latent_effect : t -> NEffect.t

val to_logic_type : t -> t

val tlsubst : Name.t list -> t list -> t -> t
val rlsubst : Name.t list -> Name.t list -> t -> t
val app : Name.t -> (t,Name.t,NEffect.t) Inst.t -> t

val equal : t -> t -> bool

module Generalize : sig
  type t = Name.t list * Name.t list * Name.t list

  val empty : t 
  val is_empty : t -> bool

  val print : t Myformat.fmt
end

val allsubst : 
  Generalize.t -> t list * Name.t list * NEffect.t list -> 
    t -> t

val forty : Generalize.t * t
