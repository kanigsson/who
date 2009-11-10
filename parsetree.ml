(* This module represents the parse tree and is there uniquely to simplify the
  parser *)
module C = Const
type var = string
type rvar = string
type effvar = string
type tvar = string

type effect = rvar list * effvar list * rvar list

type ty = 
  | TVar of tvar
  | TConst of Const.ty
  | Tuple of ty * ty
  | Arrow of ty * ty * effect
  | PureArr of ty * ty
  | TApp of tvar * inst
  | Ref of rvar * ty
  | Map of effect
  | ToLogic of ty
and inst = (ty, rvar, effect) Inst.t

type t' =
  | Const of Const.t
  | Var of var
  | App of t * t * [`Infix | `Prefix ] * rvar list
  | Seq of t * t
  | Lam of 
      var * ty * t option * t * post
  | Let of bool * generalize * t * var * t * isrec
  | PureFun of var * ty * t
  | Ite of t * t * t
  | Axiom of t
  | Logic of ty
  | Annot of t * ty
  | TypeDef of generalize * ty option * var * t
  | Quant of [`FA | `EX] * var * ty * t
  | Param of ty * effect
  | For of var * t option * var * var * var * t
  | LetReg of rvar list * t
  | Section of var * string option * t
  | EndSec of t
and t = { v : t' ; loc : Loc.loc }
and post = 
  | PNone
  | PPlain of t
  | PResult of var * t
and isrec = Rec of ty | NoRec
and generalize = tvar list * rvar list * effvar list

let mk v loc = { v = v; loc = loc }
let app ?(kind=`Prefix) t1 t2 = mk (App (t1,t2, kind,[]))
let cap_app t1 t2 cap = mk (App(t1,t2,`Prefix,cap))
let var s = mk (Var s)
let const c = mk (Const c)
let app2 s t1 t2 loc = app (app (var s loc) t1 loc) t2 loc
let appi s t1 t2 loc = app ~kind:`Infix (app (var s loc) t1 loc) t2 loc
let let_ ?(prelude=false) l e1 x e2 r = mk (Let (prelude,l,e1,x,e2,r)) 
let lam x t p e q = mk (Lam (x,t,p,e,q))
let pure_lam x t e = mk (PureFun (x,t,e))
let typedef l t x e = mk (TypeDef (l,t,x,e))
let quant k x t e = mk (Quant (k,x,t,e))

(* concatenate two abstract programs *)
let concat t1 t2 =
  let rec aux' = function
    | Const Const.Void -> t2.v
    | Let (p,g,t1,x,t2,r) -> Let (p,g,t1,x,aux t2,r)
    | TypeDef (g,t,x,t2) -> TypeDef (g,t,x,aux t2)
    | Section (n,f,t) -> Section (n,f,aux t)
    | EndSec t -> EndSec (aux t)
    | LetReg (rl,t) -> LetReg (rl, aux t)
    | _ -> assert false 
  and aux t = { t with v = aux' t.v } in
  aux t1

open Myformat

let print_ty fmt t = 
  let rec pt fmt = function
  | TVar v -> pp_print_string fmt v
  | TConst c -> Const.print_ty fmt c
  | Tuple (t1,t2) -> fprintf fmt "(%a * %a)" pt t1 pt t2
  | PureArr (t1,t2) -> fprintf fmt "(%a -> %a)" pt t1 pt t2
  | Arrow (t1,t2,_) -> fprintf fmt "(%a ->{...} %a)" pt t1 pt t2
  | Ref _ -> pp_print_string fmt "ref(...)"
  | Map _ -> pp_print_string fmt "<...>"
  | TApp (v,_) -> fprintf fmt "app(%s)" v
  | ToLogic t -> fprintf fmt "[[ %a ]]" pt t in
  pt fmt t
