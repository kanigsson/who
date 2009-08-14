open Vars

type t' =
  | Const of Const.t
  | Var of var
  | App of t * t
  | Lam of var * Ty.t * t * t option
  | Let of (tvar list * rvar list * effvar list) * t * var * t
and t = { v : t' ; mutable t : Unify.node }

val mk_node : t' -> t

val print : t Myformat.fmt
