type t =
  | Const of Ast.const
  | Var of string
  | App of t * t
  | Lam of string * t
  | Let of t * string * t

type ty = 
  [
    | `Const of Ty.const
    | `Var of string
    | `Arrow of ty * ty
    | `Tuple of ty * ty
  ]

val print : t Misc.fmt

val internalize : t -> unit Ast.t
