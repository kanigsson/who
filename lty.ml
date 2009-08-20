open Vars

type ('a,'b) t'' = 
    [
          | `Const of Const.ty
          | `Var of 'b
          | `Arr of 'a * 'a
          | `Tuple of 'a * 'a
          | `App of 'b * 'a list
    ]

type 'a t' = ('a,TyVar.t) t''
type t = [ `U of t t' ]


let arr t1 t2 = `U (`Arr (t1,t2))
let app v t2 = `U (`App (v,t2))
let tuple t1 t2 = `U (`Tuple (t1,t2))
let const c = `U (`Const c)
let var v = `U (`Var v)

let prop = const Const.TProp
let int  = const Const.TInt
let bool = const Const.TBool
let unit = const Const.TUnit

let map' r ~tyvarfun = function
  | (`Const _ as t) -> t
  | `Tuple (t1,t2) -> `Tuple (r t1, r t2)
  | `Arr (t1,t2) -> `Arr (r t1, r t2)
  | `Var v -> tyvarfun v
  | `App (v,tl) -> `App (v, List.map r tl)
let map ~tyvarfun t = 
  let rec aux (`U t) = `U (map' aux ~tyvarfun t) in
  aux t

let refresh s t =
  map ~tyvarfun:(fun v -> `Var (TyVar.refresh s v)) t

open Myformat

let print'' pra prb fmt = function
  | `Const c -> Const.print_ty fmt c
  | `Arr (t1,t2) -> fprintf fmt "(@[%a@ ->@ %a@])" pra t1 pra t2
  | `Tuple (t1,t2) -> fprintf fmt "(@[%a@ *@ %a@])" pra t1 pra t2
  | `Var v -> prb fmt v
  | `App (v,tl) -> 
      fprintf fmt "(%a %a)" prb v (print_list space pra) tl

let print' pr fmt x = print'' pr TyVar.print fmt x

let rec print fmt (`U t) = print' print fmt t

let print_list = print_list comma print

let compare' cmp a b = 
  match a,b with 
  | `Var v1, `Var v2 -> TyVar.compare v1 v2
  | `Const c1, `Const c2 -> Pervasives.compare c1 c2
  | `Tuple (ta1, ta2), `Tuple (tb1,tb2)
  | `Arr (ta1,ta2), `Arr (tb1,tb2) ->
      let c = cmp ta1 tb1 in
      if c = 0 then cmp ta2 tb2 else c
  | `App (v1,tl1), `App (v2,tl2) ->
      let c = TyVar.compare v1 v2 in
      if c = 0 then Misc.list_compare cmp tl1 tl2 else c
  | `Var _, _ -> 1
  | _, `Var _ -> -1
  | `Const _, _ -> 1
  | _, `Const _ -> -1
  | `Tuple _, _ -> 1
  | _, `Tuple _ -> -1
  | `App _, _ -> 1
  | _, `App _ -> -1

let rec compare (`U a) (`U b) = compare' compare a b

let equal a b = compare a b = 0

let binder fmt (v,t) = fprintf fmt "@[%a@ :@ %a@]" Var.print v print t


let tysubst tv (`U t) lt = 
    map ~tyvarfun:(fun v -> if TyVar.equal v tv then t else `Var v) lt


let ltysubst = List.fold_right2 tysubst

module Scheme = 
struct
  type lty = t
  type t = lty TyVar.listbind

  let open_ =TyVar.open_listbind refresh
  let close = TyVar.close_listbind
  let lty lt = close [] lt

  let print' fmt s = 
    let tl, t = open_ s in
    Format.fprintf fmt "[%a].%a" TyVar.print_list tl print t 

  let instance ts tyl = 
    let tl, t = open_ ts in
    ltysubst tl tyl t

  let print = print'

end

let well_formed' wf arity = function
    | `Const _ -> true
    | `Arr (t1,t2)
    | `Tuple (t1,t2) -> wf t1 && wf t2
    | `Var v when arity v = 0 -> true
    | `App (v, l) when arity v = List.length l -> List.for_all wf l
    | _ -> false

let well_formed arity t = 
  let rec aux (`U t) = well_formed' aux arity t in 
  aux t

