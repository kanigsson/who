open Vars

type ('a,'b) t'' = 
  [
    | `Const of Const.ty
    | `Var of 'b
    | `Arr of 'a * 'a
    | `Tuple of 'a * 'a
    | `App of 'b * 'a list
  ]

type 'a t' = ('a,TyVar.t) t''
type t = [ `U of t t' ]

val map' : ('a -> 'b) -> tyvarfun:(TyVar.t -> ([> 'b t'] as 'd)) -> 'a t' -> 'd
val map : tyvarfun:(TyVar.t -> t t') -> t -> t

val print'': 'a Myformat.fmt -> 'b Myformat.fmt -> ('a,'b) t'' Myformat.fmt
val print' : 'a Myformat.fmt -> 'a t' Myformat.fmt

val print : t Myformat.fmt
val binder : (Var.t * t) Myformat.fmt

val var : TyVar.t -> t
val const : Const.ty -> t
val tuple : t -> t -> t
val arr : t -> t -> t
val app : TyVar.t -> t list -> t
val refresh : subst -> t -> t


val unit : t
val int : t
val bool : t
val prop : t

val compare' : ('a -> 'a -> int) -> 'a t' -> 'a t' -> int
val compare : t -> t -> int
val equal : t -> t -> bool

module Scheme : sig
  type lty = t
  type t
  val lty : lty -> t
  val instance : t -> lty list -> lty
  val open_ : t -> TyVar.t list * lty
  val close : TyVar.t list -> lty -> t
  val print : t Myformat.fmt
end

val well_formed' : ('a -> bool) -> (TyVar.t -> int) -> 'a t' -> bool
val well_formed : (TyVar.t -> int) -> t -> bool
