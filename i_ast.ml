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
  | Var of string * ut * ur * ue
  | App of t * t
  | Lam of var * Ty.t * t 
  | Let of (tvar list * rvar list * effvar list) * t * var * t
and t = { v : t' ; t : U.node ; e : U.enode }

open Format
let tyvarlist = Misc.optlist pp_print_string
let rlist = Misc.optlist pp_print_string
let elist = Misc.optlist pp_print_string

let htp fmt h =
  fprintf fmt "[";
  Hashtbl.iter (fun k v -> fprintf fmt "%s|->%a;" k U.print_node v) h;
  fprintf fmt "]"

let etp fmt h = 
  fprintf fmt "[";
  Hashtbl.iter (fun k v -> fprintf fmt "%s|->%a;" k U.preff v) h;
  fprintf fmt "]"

let rtp fmt h = 
  fprintf fmt "[";
  Hashtbl.iter (fun k v -> fprintf fmt "%s|->%a;" k U.prvar v) h;
  fprintf fmt "]"

let rec print' fmt = function
  | Const c -> Const.print fmt c
  | Var (v,tl,rl,el) -> fprintf fmt "%s%a%a%a" v htp tl rtp rl etp el
  | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam (x,t,e) -> fprintf fmt "@[(λ(%s:%a)@ ->@ %a)@]" x Ty.print t print e
  | Let ((tl,rl,el),e1,x,e2) -> 
      fprintf fmt "@[let@ %s%a%a%a=@ %a@ in@ %a@]" 
      x tyvarlist tl rlist rl elist el print e1 print e2
and print fmt t = 
  fprintf fmt "(%a : %a, %a)" print' t.v U.print_node t.t U.preff t.e
