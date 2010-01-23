(* This module represents the parse tree and is there uniquely to simplify the
  parser *)
module C = Const
type var = string
type rvar = string
type effvar = string
type tvar = string

type effect = ParseTypes.effect
type ty = ParseTypes.t

type t' =
  | Const of Const.t
  | Var of var * effect list
  | App of t * t * [`Infix | `Prefix ] * rvar list
  | Seq of t * t
  | Lam of var * ty * rvar list * t option * t * post
  | Let of generalize * t * var * t * ParseTypes.t Const.isrec
  | PureFun of var * ty * t
  | Ite of t * t * t
  | Annot of t * ty
  | Quant of [`FA | `EX] * var * ty * t
  | Param of ty * effect
  | For of var * t option * var * var * var * t
  | LetReg of rvar list * t
  | Restrict of t * effect
  | HoareTriple of t option * t * t * post
and t = { v : t' ; loc : Loc.loc }
and post = 
  | PNone
  | PPlain of t
  | PResult of var * t
and generalize = tvar list * rvar list * effvar list

type decl = 
  | Logic of var * generalize * ty
  | Axiom of string * generalize * t
  | Section of var * Const.takeover list * decl list
  | TypeDef of generalize * ty option * var
  | Program of var * generalize * t * ParseTypes.t Const.isrec
  | DLetReg of rvar list 

type theory = decl list

let mk v loc = { v = v; loc = loc }
let app ?(kind=`Prefix) t1 t2 = mk (App (t1,t2, kind,[]))
let cap_app t1 t2 cap = mk (App(t1,t2,`Prefix,cap))
let var ?(inst=[]) s = mk (Var (s,inst))
let const c = mk (Const c)
let app2 s t1 t2 loc = app (app (var s loc) t1 loc) t2 loc
let appi s t1 t2 loc = app ~kind:`Infix (app (var s loc) t1 loc) t2 loc
let let_ l e1 x e2 r = mk (Let (l,e1,x,e2,r)) 
let lam x t p e q = mk (Lam (x,t,[],p,e,q))
let lamcap x t c p e q = mk (Lam (x, t, c, p, e, q))
let pure_lam x t e = mk (PureFun (x,t,e))
let quant k x t e = mk (Quant (k,x,t,e))

