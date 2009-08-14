type var = string
type tvar = string
type rvar = string
type effvar = string

module U = Unify

type ('a,'b,'c) t' =
  | Const of Const.t
  | Var of string * ('a,'b,'c) Inst.t
  | App of ('a,'b,'c) t * ('a,'b,'c) t
  | Lam of var * Ty.t * ('a,'b,'c) t * ('a,'b,'c) t option
  | Let of Generalize.t * ('a,'b,'c) t * var * ('a,'b,'c) t
and ('a,'b,'c) t = { v :('a,'b,'c)  t' ; t : 'a ; e : 'c }
type infer = (U.node, U.rnode, U.enode) t'
type recon = (Ty.t, rvar, Effect.t) t'

let mk v t e = { v = v; t = t; e = e }
let mk_val v t = mk v t (U.new_e ())

open Myformat

let print pra prb prc fmt t = 
  let rec print' fmt = function
    | Const c -> Const.print fmt c
    | Var (v,i) -> fprintf fmt "%s %a" v (Inst.print pra prb prc) i
    | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
    | Lam (x,t,e,p) -> fprintf fmt "@[(λ(%s:%a)@ ->@ %a%a)@]" 
      x Ty.print t print e post p
    | Let (g,e1,x,e2) -> 
        fprintf fmt "@[let@ %s %a=@ %a@ in@ %a@]" 
        x Generalize.print g print e1 print e2
  and print fmt t = print' fmt t.v
  and post fmt = function
    | None -> ()
    | Some x -> fprintf fmt "{%a}" print x in 
  print fmt t

module Infer = struct
  let const c = mk_val (Const c) (U.const (Const.type_of_constant c))

  let lam x t e p = mk_val (Lam (x,U.to_ty t,e,p)) (U.arrow t e.t e.e)
  let lam_anon t e p = lam "__anon" t e p

  let print fmt t = print U.print_node U.prvar U.preff fmt t
end

module Recon = struct
  let print fmt t = print Ty.print Vars.rvar Effect.print fmt t
end

