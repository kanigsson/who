type t =
  | Const of A.const
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

open Format
let rec print fmt = function
  | Const c -> A.print_const fmt c
  | Var s -> pp_print_string fmt s
  | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam (s,t) -> fprintf fmt "@[(λ%s@ ->@ %a)@]" s print t
  | Let (t,s,t') -> fprintf fmt "@[let@ %s@ =@ %a@ in@ %a@]" s print t print t'

module SM = Misc.StringMap
open Vars

let new_var env x = 
  let nv = Var.from_string x in
  SM.add x nv env, nv

exception Error of string

let error s = raise (Error s)
let internalize env t = 
  let rec aux' env = function
    | Const c -> A.Const c
    | Var s -> 
        begin try A.Var (SM.find s env)
        with Not_found -> error (Misc.mysprintf "unknown variable : %s" s) end
    | App (t1,t2) -> A.App (aux env t1, aux env t2)
    | Lam (s,t) ->
        let env, x = new_var env s in
        A.Lam (close_bind x (aux env t))
    | Let (t,s,t') ->
        let t = aux env t in
        let env, x = new_var env s in
        A.Let (t, close_bind x (aux env t')) 
  and aux env t = { A.v = aux' env t; t = () } in
  aux env t

let internalize = internalize Initial.intern_map
