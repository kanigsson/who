type var = string
type tvar = string
type rvar = string
type t' =
  | Const of Const.t
  | Var of string * Ty.t list * rvar list
  | App of t * t
  | Lam of var * Ty.t * t 
  | Let of (tvar list * rvar list) * t * var * t
and t = { v : t' ; t : Ty.t }

open Format
let tyvarlist = Misc.optlist pp_print_string
let tylist = Misc.optlist Ty.print
let rlist = Misc.optlist pp_print_string

let rec print' fmt = function
  | Const c -> Const.print fmt c
  | Var (v,tl,rl) -> fprintf fmt "%s%a%a" v tylist tl rlist rl
  | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam (x,t,e) -> fprintf fmt "@[(λ(%s:%a)@ ->@ %a)@]" x Ty.print t print e
  | Let ((tl,rl),e1,x,e2) -> 
      fprintf fmt "@[let@ %s%a%a=@ %a@ in@ %a@]" 
      x tyvarlist tl rlist rl print e1 print e2
and print fmt t = fprintf fmt "(%a : %a)" print' t.v Ty.print t.t
