type t' =
  | Const of Const.t
  | Var of string
  | App of t * t
  | Lam of string * t
  | Let of t * string * t
and t = { v : t' ; mutable t : Unify.ty    }

val mk_node : t' -> t

val print : t Misc.fmt
