type effect = string list * string list 

type t = 
  | TVar of string
  | TConst of Const.ty
  | Tuple of t * t
  | Arrow of t * t * effect * string list
  | PureArr of t * t
  | TApp of string * (t,string,effect) Inst.t
  | Ref of string * t
  | Map of effect
  | ToLogic of t

open Myformat

let print fmt t = 
  let rec pt fmt = function
  | TVar v -> pp_print_string fmt v
  | TConst c -> Const.print_ty fmt c
  | Tuple (t1,t2) -> fprintf fmt "(%a * %a)" pt t1 pt t2
  | PureArr (t1,t2) -> fprintf fmt "(%a -> %a)" pt t1 pt t2
  | Arrow (t1,t2,_,_) -> fprintf fmt "(%a ->{...} %a)" pt t1 pt t2
  | Ref _ -> pp_print_string fmt "ref(...)"
  | Map _ -> pp_print_string fmt "<...>"
  | TApp (v,_) -> fprintf fmt "app(%s)" v
  | ToLogic t -> fprintf fmt "[[ %a ]]" pt t in
  pt fmt t
