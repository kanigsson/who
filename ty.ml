open Vars
type t = 
    Const of Const.ty
    | Var of TyVar.t
    | Arrow of t * t
    | Tuple of t * t

let map ~tyvarfun t = 
  let rec aux = function
  | (Const _) as t -> t
  | Var v -> tyvarfun v
  | Arrow (t1,t2) -> Arrow (aux t1, aux t2)
  | Tuple (t1,t2) -> Tuple (aux t1, aux t2)
  in aux t

let refresh s t = map ~tyvarfun:(fun v -> Var (TyVar.refresh s v)) t

open Format
let rec print fmt = function
  | Const c -> Const.print_ty fmt c
  | Var v -> TyVar.print fmt v
  | Arrow (t1,t2) -> fprintf fmt "@[(%a@ ->@ %a)@]" print t1 print t2
  | Tuple (t1,t2) -> fprintf fmt "@[(%a,@ %a)@]" print t1 print t2

let var v = Var v
let arrow t1 t2 = Arrow (t1,t2)
let const c = Const c

let unit = const (Const.TUnit)

let arg = function
  | Arrow (t1,_) -> t1
  | _ -> assert false

let rec equal t1 t2 = 
  match t1, t2 with
  | Tuple (t1a,t2a), Tuple (t1b,t2b) 
  | Arrow (t1a,t2a), Arrow (t1b,t2b) -> 
      equal t1a t1b && equal t2a t2b
  | Const c1, Const c2 -> c1 = c2
  | Var v1, Var v2 -> TyVar.equal v1 v2
  | _, _ -> false
