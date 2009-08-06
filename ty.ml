open Vars
type const = 
  | Bool
  | Int
  | Unit

type 'a t' = 
  [
    | `Const of const
    | `Var of TyVar.t
    | `Arrow of 'a * 'a
    | `Tuple of 'a * 'a
  ]

type t = [ `U of t t' ]

let map' r ~tyvarfun = function
  | (`Const _) as t -> t
  | `Var v -> tyvarfun v
  | `Arrow (t1,t2) -> `Arrow (r t1, r t2)
  | `Tuple (t1,t2) -> `Tuple (r t1, r t2)

let map ~tyvarfun t =
  let rec aux  (`U t) = `U (map' ~tyvarfun aux t) in
  aux t

let refresh s t = 
  map ~tyvarfun:(fun v -> `Var (TyVar.refresh s v)) t

open Format
let print_const fmt = function
  | Bool -> pp_print_string fmt "bool"
  | Int -> pp_print_string fmt "int"
  | Unit -> pp_print_string fmt "unit"

let print' pr fmt = function
  | `Const c -> print_const fmt c
  | `Var v -> TyVar.print fmt v
  | `Arrow (t1,t2) -> fprintf fmt "@[(%a@ ->@ %a)@]" pr t1 pr t2
  | `Tuple (t1,t2) -> fprintf fmt "@[(%a,@ %a)@]" pr t1 pr t2
let rec print fmt (`U t) = print' print fmt t

let var v = `U (`Var v)
let arrow t1 t2 = `U (`Arrow (t1,t2))
let const c = `U (`Const c)

