type tvar = string
type var = string
type rvar = string
type effvar = string

type t' =
  | Const of Const.t
  | Var of var
  | App of t * t
  | Lam of var * Ty.t * t
  | Let of (tvar list * rvar list * effvar list) * t * var * t
and t = { v : t' ; mutable t : Unify.node }

val mk_node : t' -> t

val print : t Misc.fmt
