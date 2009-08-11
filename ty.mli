type tvar = string
type 'a t' = 
  | Var of string
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a
type t = C of t t'

val print : t Misc.fmt
val print' : 'a Misc.fmt -> ('a t') Misc.fmt

val var : tvar -> t
val const : Const.ty -> t
val arrow : t -> t -> t
val tuple : t -> t -> t
val unit : t

val arg : t -> t

val subst : tvar -> t -> t -> t
val lsubst : tvar list -> t list -> t -> t
