open Vars

type t' =
  | Const of Const.t
  | Var of Var.t
  | App of t * t
  | Lam of Ty.t * t Var.bind
  | Let of t TyVar.listbind * t Var.bind 
and t = { v : t' ; t : Ty.t }

let map ~varfun ~varbindfun ~tyfun ~tylistbindfun t = 
  let rec aux' = function
    | (Const _) as t -> t
    | Var v -> varfun v
    | App (t1,t2) -> App (aux t1, aux t2)
    | Lam (t,b) -> Lam (tyfun t, varbindfun b)
    | Let (t,b) -> Let (tylistbindfun t, varbindfun b) 
  and aux t = { v = aux' t.v; t = tyfun t.t } in
  aux t

let rec refresh s t = 
  map ~varfun:(fun x -> Var (Var.refresh s x)) 
      ~varbindfun:(Var.refresh_bind s) ~tyfun:(Ty.refresh s) 
      ~tylistbindfun:(TyVar.refresh_listbind s) t

let open_bind b = Var.open_bind refresh b
let close_bind = Var.close_bind
let open_tygen = TyVar.open_listbind refresh
let close_tygen = TyVar.close_listbind

open Format
let tyvarlist fmt = function
  | [] -> Misc.space fmt ()
  | l -> fprintf fmt "@ [%a]@ " (Misc.print_list Misc.space TyVar.print) l

let rec print' fmt = function
  | Const c -> Const.print fmt c
  | Var v -> Var.print fmt v
  | App (t1,t2) -> 
      fprintf fmt "@[(%a@ %a)@]" print t1 print t2
  | Lam (t,b) -> 
      let x,e = open_bind b in
      fprintf fmt "@[(λ(%a:%a)@ ->@ %a)@]" Var.print x Ty.print t print e
  | Let (g,b) -> 
      let x,e2 = open_bind b in
      let tl,e1 = open_tygen g in
      fprintf fmt "@[let@ %a%a=@ %a@ in@ %a@]" 
        Var.print x tyvarlist tl print e1 print e2
and print fmt t = fprintf fmt "(%a : %a)" print' t.v Ty.print t.t
