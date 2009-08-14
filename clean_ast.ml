open Vars
type t' =
  | Const of Const.t
  | Var of var
  | App of t * t
  | Lam of var * Ty.t * t * t option
  | Let of Generalize.t * t * var * t
and t = { v : t' ; mutable t : Unify.node }

let dummy = Unify.new_ty ()
let mk_node v = { v = v; t = dummy }

open Format

let rec print' fmt = function
  | Const c -> Const.print fmt c
  | Var s -> pp_print_string fmt s
  | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam (s,ty,t,p) -> 
      fprintf fmt "@[(λ(%s:%a)@ ->@ %a%a)@]" s Ty.print ty print t post p
  | Let (g,t,s,t') -> 
      fprintf fmt "@[let@ %s %a =@ %a@ in@ %a@]" s 
        Generalize.print g print t print t'
and print fmt t = print' fmt t.v
and post fmt = function
  | None -> ()
  | Some x -> fprintf fmt " {%a}" print x



