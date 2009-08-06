
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

let map ~varfun ~varbindfun t = 
  let rec aux = function
    | (Const _) as t -> t
    | Var v -> varfun v
    | App (t1,t2) -> App (aux t1, aux t2)
    | Lam b -> Lam (varbindfun b)
    | Let (t,b) -> Let (aux t, varbindfun b) in
  aux t

let rec refresh s t = 
  map ~varfun:(fun x -> Var (Var.refresh s x)) 
      ~varbindfun:(Var.refresh_bind s) t

let open_bind = Var.open_bind refresh
let close_bind = Var.close_bind

open Format
let print_const fmt = function
  | Int i -> pp_print_int fmt i
  | Void -> pp_print_string fmt "()"
  | Btrue -> pp_print_string fmt "true"
  | Bfalse -> pp_print_string fmt "false"

let rec print fmt = function
  | Const c -> print_const fmt c
  | Var v -> Var.print fmt v
  | App (t1,t2) -> 
      fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam b -> 
      let x,t = open_bind b in
      fprintf fmt "@[(λ%a@ ->@ %a)@]" Var.print x print t
  | Let (t,b) -> 
      let x,t' = open_bind b in
      fprintf fmt "@[let@ %a@ =@ %a@ in@ %a@]" Var.print x print t print t'
