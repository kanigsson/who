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
and inst = (ty, rvar, effect) Inst.t

type t' =
  | Const of Const.t
  | Var of var
  | App of t * t * Const.fix * rvar list
  | Seq of t * t
  | Lam of 
      var * ty * t option * t * post
  | Let of generalize * t * var * t * isrec
  | PureFun of var * ty * t
  | Ite of t * t * t
  | Axiom of t
  | Logic of ty
  | Annot of t * ty
  | TypeDef of generalize * ty option * var * t
  | Quant of C.quant * var * ty * t
  | Param of ty * effect
  | For of var * t option * var * var * var * t
  | LetReg of rvar list * t
and t = { v : t' ; loc : Loc.loc }
and post = 
  | PNone
  | PPlain of t
  | PResult of var * t
and isrec = Rec of ty | NoRec
and generalize = tvar list * rvar list * effvar list

let mk v loc = { v = v; loc = loc }
let app ?(kind=C.Prefix) t1 t2 = mk (App (t1,t2, kind,[]))
let cap_app t1 t2 cap = mk (App(t1,t2,C.Prefix,cap))
let var s = mk (Var s)
let const c = mk (Const c)
let app2 s t1 t2 loc = app (app (var s loc) t1 loc) t2 loc
let appi s t1 t2 loc = app ~kind:C.Infix (app (var s loc) t1 loc) t2 loc
let let_ l e1 x e2 r = mk (Let (l,e1,x,e2,r)) 
let lam x t p e q = mk (Lam (x,t,p,e,q))
let pure_lam x t e = mk (PureFun (x,t,e))
let typedef l t x e = mk (TypeDef (l,t,x,e))
let quant k x t e = mk (Quant (k,x,t,e))

let concat t1 t2 =
  let rec aux' = function
    | Const Const.Void -> t2.v
    | Let (g,t1,x,t2,r) -> Let (g,t1,x,aux t2,r)
    | TypeDef (g,t,x,t2) -> TypeDef (g,t,x,aux t2)
    | _ -> assert false 
  and aux t = { t with v = aux' t.v } in
  aux t1
