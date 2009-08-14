type tvar = string
type rvar = string
type effvar = string
type ('a,'b,'c) t' = 
  | Var of string
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c
  | PureArr of 'a * 'a
  | Ref of 'b * 'a
  | Map of 'c
type t = C of (t,rvar,Effect.t) t'

open Myformat

let print' pt pr pe fmt = function
  | Var x -> pp_print_string fmt x
  | Arrow (t1,t2,eff) -> 
      fprintf fmt "(%a ->%a %a)" pt t1 pe eff pt t2
  | PureArr (t1,t2) -> 
      fprintf fmt "(%a ->%a)" pt t1 pt t2
  | Tuple (t1,t2) -> fprintf fmt "(%a *@ %a)" pt t1 pt t2
  | Const c -> Const.print_ty fmt c
  | Ref (r,t) -> fprintf fmt "ref(%a,%a)" pr r pt t
  | Map e -> fprintf fmt "map%a" pe e

let rec print fmt (C x) = 
  print' print pp_print_string Effect.print fmt x

let print_list sep fmt t = print_list sep print fmt t

let var v = C (Var v)
let arrow t1 t2 eff = C (Arrow (t1,t2,eff))
let parr t1 t2 = C (PureArr (t1,t2))
let tuple t1 t2 = C (Tuple (t1,t2))
let const c = C (Const c)
let ref_ r t = C (Ref (r,t))
let map e = C (Map e)

let unit = const (Const.TUnit)
let prop = const (Const.TProp)

let arg = function
  | C (Arrow (t1,_,_)) -> t1
  | _ -> assert false

let subst x t target =
  let rec aux' = function
    | Var y when x = y -> let C t = t in t
    | (Var _ | Const _ | Map _) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff) -> Arrow (aux t1, aux t2,eff) 
    | Ref (r,t) -> Ref (r,aux t)
  and aux (C x) = C (aux' x) in
  aux target

let rsubst x t target =
  let rec aux' = function
    | (Var _ | Const _) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff) -> Arrow (aux t1, aux t2,effsubst eff) 
    | Ref (r,t) -> Ref (auxr r,aux t)
    | Map e -> Map (effsubst e)
  and auxr r = if r = x then t else r
  and effsubst (rl,el) = Effect.map auxr rl, el
  and aux (C x) = C (aux' x) in
  aux target

let esubst e eff target = 
  let rec aux' = function
    | (Var _ | Const _) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff') -> Arrow (aux t1, aux t2,Effect.subst e eff eff') 
    | Ref (r,t) -> Ref (r,aux t)
    | Map eff' -> Map (Effect.subst e eff eff')
  and aux (C x) = C (aux' x) in
  aux target

let lsubst = List.fold_right2 subst
let rlsubst = List.fold_right2 rsubst
let elsubst = List.fold_right2 esubst

let allsubst (tvl,rvl,evl) (tl,rl,el) target = 
  elsubst evl el (rlsubst rvl rl (lsubst tvl tl target))

let rec equal' t1 t2 = 
  match t1, t2 with
  | Var x1, Var x2 -> x1 = x2
  | Const x1, Const x2 -> x1 = x2
  | Tuple (ta1,ta2), Tuple (tb1,tb2)
  | PureArr (ta1,ta2), PureArr (tb1,tb2) -> 
      equal ta1 tb1 && equal ta2 tb2
  | Arrow (ta1,ta2,e1), Arrow (tb1,tb2,e2) -> 
      equal ta1 tb1 && equal ta2 tb2 && Effect.equal e1 e2
  | Ref (r1,t1), Ref (r2,t2) -> r1 = r2 && equal t1 t2
  | _ -> false
and equal (C a) (C b) = equal' a b
