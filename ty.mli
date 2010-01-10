type ('a,'b,'c) t' = 
  | Var of Name.t
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c * 'b list
  | PureArr of 'a * 'a
  | App of Name.t * ('a,'b,'c) Inst.t
  | Ref of 'b * 'a
  | Map of 'c
type t = C of (t,Name.t,NEffect.t) t'

val print : t Myformat.fmt
val print_list : 
  unit Myformat.fmt -> t list Myformat.fmt
val print' : ?kind:[`Coq | `Who | `Pangoline ] -> 'a Myformat.fmt -> 
  'b Myformat.fmt -> 'c Myformat.fmt -> ('a -> bool) -> (('a ,'b,'c) t') Myformat.fmt

val varprint : [`Coq | `Who | `Pangoline ] -> Name.t Myformat.fmt


val coq_print : t Myformat.fmt

val gen_print : [`Coq | `Who | `Pangoline ] -> t Myformat.fmt

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
val emptymap : t

val arg : t -> t
val result : t -> t
val latent_effect : t -> NEffect.t
val domain : t -> NEffect.t
val is_map : t -> bool
val is_ref : t -> bool
val destr_tuple : t -> t * t

val to_logic_type : t -> t

val tlsubst : Name.t list -> t list -> t -> t
val rlsubst : Name.t list -> Name.t list -> t -> t
val elsubst : Name.t list -> NEffect.t list -> t -> t
val rsubst : Name.t list -> Name.t list -> Name.t -> Name.t
val app : Name.t -> (t,Name.t,NEffect.t) Inst.t -> t

val equal : t -> t -> bool

module Generalize : sig
  type t = Name.t list * Name.t list * Name.t list
  type 'a bind = 'a Name.listbind Name.listbind Name.listbind

  val empty : t 
  val is_empty : t -> bool

  val print : t Myformat.fmt
  val open_ : (Name.subst -> 'a -> 'a) -> 'a bind -> t * 'a
  val sopen_ : 'a bind -> t * 'a
  val close : t -> 'a -> 'a bind 

  val equal : t -> t -> bool

  val get_first : t -> Name.t
end

val allsubst : 
  Generalize.t -> t list * Name.t list * NEffect.t list -> 
    t -> t

val forty : Generalize.t * t

val find_type_of_r : Name.t -> t -> t option

val get_reg : t -> Name.t

val selim_map : (Name.t -> t) -> t -> t

val pretype : t -> NEffect.t -> t
val posttype : t -> t -> NEffect.t -> t
val prepost_type: t -> t -> NEffect.t -> t

module Predef : sig
  val prop_2 : t
  val prop_3 : t
  val bool_3 : t
  val int_3 : t
  val iip : t
  val iib : t
  val aap : Generalize.t * t
  val aab : Generalize.t * t
  val mk_tuple : Generalize.t * t

  val fst : Generalize.t * t
  val snd : Generalize.t * t
end
