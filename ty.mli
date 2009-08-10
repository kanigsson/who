open Vars
type t = 
    | Const of Const.ty
    | Var of TyVar.t
    | Arrow of t * t
    | Tuple of t * t

val print : t Misc.fmt

val var : TyVar.t -> t
val const : Const.ty -> t
val arrow : t -> t -> t
val unit : t

val arg : t -> t

val map : tyvarfun:(TyVar.t -> t) -> t -> t
val refresh : subst -> t -> t

val equal : t -> t -> bool
