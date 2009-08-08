open Vars
type 'a t' = 
  [
    | `Const of Const.ty
    | `Var of TyVar.t
    | `Arrow of 'a * 'a
    | `Tuple of 'a * 'a
  ]

type t = [ `U of t t' ]

val print : t Misc.fmt

val var : TyVar.t -> t
val const : Const.ty -> t
val arrow : t -> t -> t
val unit : t

val arg : t -> t

val map : tyvarfun:(TyVar.t -> t t') -> t -> t
val refresh : subst -> t -> t
