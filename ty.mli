open Vars
type const = 
  | Bool
  | Int
  | Unit

type 'a t' = 
  [
    | `Const of const
    | `Var of TyVar.t
    | `Arrow of 'a * 'a
    | `Tuple of 'a * 'a
  ]

type t = [ `U of t t' ]

val print_const : const Misc.fmt
val print : t Misc.fmt

val var : TyVar.t -> t
val const : const -> t
val arrow : t -> t -> t

val map : tyvarfun:(TyVar.t -> t t') -> t -> t
val refresh : subst -> t -> t
