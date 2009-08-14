type var = string
type tvar = string
type rvar = string
type effvar = string

module U = Unify
type ut = (tvar, U.node) Hashtbl.t
type ur = (rvar, U.rnode) Hashtbl.t
type ue = (effvar, U.enode) Hashtbl.t

type t' =
  | Const of Const.t
  | Var of string * inst
  | App of t * t
  | Lam of var * Ty.t * t * t option
  | Let of Generalize.t * t * var * t
and t = { v : t' ; t : U.node ; e : U.enode }
and inst = (ut,ur,ue) Inst.t

let mk v t e = { v = v; t = t; e = e }
let mk_val v t = mk v t (U.new_e ())

open Myformat

let htp = hash_print pp_print_string U.print_node
let rtp = hash_print pp_print_string U.prvar
let etp = hash_print pp_print_string U.preff

let rec print' fmt = function
  | Const c -> Const.print fmt c
  | Var (v,i) -> fprintf fmt "%s %a" v inst i
  | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam (x,t,e,p) -> fprintf fmt "@[(λ(%s:%a)@ ->@ %a%a)@]" 
    x Ty.print t print e post p
  | Let (g,e1,x,e2) -> 
      fprintf fmt "@[let@ %s %a=@ %a@ in@ %a@]" 
      x Generalize.print g print e1 print e2
and print fmt t = print' fmt t.v
(*   fprintf fmt "(%a : %a, %a)" print' t.v U.print_node t.t U.preff t.e *)
and post fmt = function
  | None -> ()
  | Some x -> fprintf fmt "{%a}" print x
and inst = Inst.print htp rtp etp

let const c = mk_val (Const c) (U.const (Const.type_of_constant c))

let lam x t e p = mk_val (Lam (x,U.to_ty t,e,p)) (U.arrow t e.t e.e)
let lam_anon t e p = lam "__anon" t e p
