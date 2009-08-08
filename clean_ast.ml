type t' =
  | Const of Const.t
  | Var of string
  | App of t * t
  | Lam of string * t
  | Let of t * string * t
and t = { v : t' ; mutable t : Unify.ty    }

let dummy = Unify.fresh (Unify.Var 0)
let mk_node v = { v = v; t = dummy }

open Format
let rec print' fmt = function
  | Const c -> Const.print fmt c
  | Var s -> pp_print_string fmt s
  | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam (s,t) -> fprintf fmt "@[(λ%s@ ->@ %a)@]" s print t
  | Let (t,s,t') -> fprintf fmt "@[let@ %s@ =@ %a@ in@ %a@]" s print t print t'
and print fmt t = print' fmt t.v



