open Vars

type const = 
  | Int of int
  | Void
  | Btrue
  | Bfalse

type t =
  | Const of const
  | Var of Var.t
  | App of t * t
  | Lam of t Var.bind
  | Let of t * t Var.bind 

val print_const : const Misc.fmt
val print : t Misc.fmt

val open_bind : t Var.bind -> Var.t * t
val close_bind : Var.t -> t -> t Var.bind
