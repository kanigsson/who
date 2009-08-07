
open Vars

type 'a t' =
  | Const of const
  | Var of Var.t
  | App of 'a t * 'a t
  | Lam of 'a t Var.bind
  | Let of 'a t * 'a t Var.bind 
and 'a t = { v : 'a t' ; t : 'a }

let map ~varfun ~varbindfun ~annotfun t = 
  let rec aux' = function
    | (Const _) as t -> t
    | Var v -> varfun v
    | App (t1,t2) -> App (aux t1, aux t2)
    | Lam b -> Lam (varbindfun b)
    | Let (t,b) -> Let (aux t, varbindfun b) 
  and aux t = { v = aux' t.v; t = annotfun t.t } in
  aux t

let rec refresh ~annotfun s t = 
  map ~varfun:(fun x -> Var (Var.refresh s x)) 
      ~varbindfun:(Var.refresh_bind s) ~annotfun t

open Format
let print pr open_ fmt x =
  let rec print' fmt = function
    | Const c -> print_const fmt c
    | Var v -> Var.print fmt v
    | App (t1,t2) -> 
        fprintf fmt "@[(%a@ %a)@]" print t1 print t2
    | Lam b -> 
        let x,t = open_ b in
        fprintf fmt "@[(λ%a@ ->@ %a)@]" Var.print x print t
    | Let (t,b) -> 
        let x,t' = open_ b in
        fprintf fmt "@[let@ %a@ =@ %a@ in@ %a@]" Var.print x print t print t'
  and print fmt t = 
    fprintf fmt "%a%a" print' t.v pr t.t in
  print fmt x

module DontCare = struct
  let refresh s t = refresh ~annotfun:(fun x -> x) s t
  let open_bind b = Var.open_bind refresh b
  let close_bind = Var.close_bind
  let print fmt x = print (fun _ _ -> ()) open_bind fmt x
end

module Ty = struct
  let refresh s t = refresh ~annotfun:(fun t -> Ty.refresh s t) s t
  let open_bind b = Var.open_bind refresh b
  let close_bind b = Var.close_bind b
  let print fmt x = 
    print (fun fmt t -> fprintf fmt " : %a " Ty.print t) open_bind fmt x
end
