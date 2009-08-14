open Vars
type t' =
  | Const of Const.t
  | Var of string * inst
  | App of t * t
  | Lam of var * Ty.t * t 
  | Let of Generalize.t * t * var * t
and t = { v : t' ; t : Ty.t }
and inst = (Ty.t list , rvar list , Effect.t list) Inst.t

open Myformat

let rec print' fmt = function
  | Const c -> Const.print fmt c
  | Var (v,i) -> 
      fprintf fmt "%s %a" v print_inst i
  | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam (x,t,e) -> fprintf fmt "@[(λ(%s:%a)@ ->@ %a)@]" x Ty.print t print e
  | Let (g,e1,x,e2) -> 
      fprintf fmt "@[let@ %s%a=@ %a@ in@ %a@]" 
      x Generalize.print g print e1 print e2
and print fmt t = fprintf fmt "(%a : %a)" print' t.v Ty.print t.t
and print_inst = 
  Inst.print (Ty.print_list comma) (print_list comma rvar) 
             (Effect.print_list comma)
