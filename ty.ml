type tvar = string
type rvar = string
type ('a,'b) t' = 
  | Var of string
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a
  | Ref of 'b * 'a
type t = C of (t,rvar) t'

open Format
let print' pt pr fmt = function
  | Var x -> pp_print_string fmt x
  | Arrow (t1,t2) -> fprintf fmt "(%a -> %a)" pt t1 pt t2
  | Tuple (t1,t2) -> fprintf fmt "(%a,@ %a)" pt t1 pt t2
  | Const c -> Const.print_ty fmt c
  | Ref (r,t) -> fprintf fmt "ref(%a,%a)" pr r pt t

let rec print fmt (C x) = print' print pp_print_string fmt x

let var v = C (Var v)
let arrow t1 t2 = C (Arrow (t1,t2))
let tuple t1 t2 = C (Tuple (t1,t2))
let const c = C (Const c)
let ref_ r t = C (Ref (r,t))

let unit = const (Const.TUnit)

let arg = function
  | C (Arrow (t1,_)) -> t1
  | _ -> assert false

let subst x t target =
  let rec aux' = function
    | Var y when x = y -> let C t = t in t
    | (Var _ | Const _) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | Arrow (t1,t2) -> Arrow (aux t1, aux t2) 
    | Ref (r,t) -> Ref (r,aux t)
  and aux (C x) = C (aux' x) in
  aux target

let rsubst x t target =
  let rec aux' = function
    | (Var _ | Const _) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | Arrow (t1,t2) -> Arrow (aux t1, aux t2) 
    | Ref (r,t) -> Ref (auxr r,aux t)
  and auxr r = if r = x then t else r
  and aux (C x) = C (aux' x) in
  aux target

let lsubst = List.fold_right2 subst

let rlsubst = List.fold_right2 rsubst
