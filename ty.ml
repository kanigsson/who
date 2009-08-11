type tvar = string
type 'a t' = 
  | Var of string
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a
type t = C of t t'

open Format
let print' pr fmt = function
  | Var x -> pp_print_string fmt x
  | Arrow (t1,t2) -> fprintf fmt "(%a -> %a)" pr t1 pr t2
  | Tuple (t1,t2) -> fprintf fmt "(%a,@ %a)" pr t1 pr t2
  | Const c -> Const.print_ty fmt c

let rec print fmt (C x) = print' print fmt x

let var v = C (Var v)
let arrow t1 t2 = C (Arrow (t1,t2))
let tuple t1 t2 = C (Tuple (t1,t2))
let const c = C (Const c)

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
  and aux (C x) = C (aux' x) in
  aux target

let lsubst = List.fold_right2 subst
