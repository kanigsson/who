type tvar = string
type var = string
type rvar = string

type t' =
  | Const of Const.t
  | Var of var
  | App of t * t
  | Lam of var * Ty.t * t
  | Let of (tvar list * rvar list) * t * var * t
and t = { v : t' ; mutable t : Unify.node }

let dummy = Unify.new_ty ()
let mk_node v = { v = v; t = dummy }

open Format

let print_tyvlist = Misc.optlist pp_print_string

let rec print' fmt = function
  | Const c -> Const.print fmt c
  | Var s -> pp_print_string fmt s
  | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam (s,ty,t) -> 
      fprintf fmt "@[(λ(%s:%a)@ ->@ %a)@]" s Ty.print ty print t
  | Let ((tl,rl),t,s,t') -> 
      fprintf fmt "@[let@ %s%a%a =@ %a@ in@ %a@]" s 
        print_tyvlist tl print_tyvlist rl print t print t'
and print fmt t = print' fmt t.v



