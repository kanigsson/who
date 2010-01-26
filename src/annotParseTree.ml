type tyvar = string
type var = string
type rvar = string
type effvar = string

type generalize = tyvar list * rvar list * effvar list

type effect = ParseTypes.effect
type ty = ParseTypes.t

type t' =
  | Const of Const.t
  | Var of var * (ty,rvar,effect) Inst.t
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t * [`Infix | `Prefix ] * rvar list
  | Lam of var * ty * rvar list * t * t * t 
  (* boolean which describes if the let comes from the prelude or not *)  
  | Let of generalize * t * var * t * ParseTypes.t Const.isrec
  | LetReg of rvar list * t
  | PureFun of ty * var * t
  | Ite of t * t * t
  | Annot of t * ty
  | Quant of [`FA | `EX ] * ty * var * t
  | HoareTriple of t * t * t
  | Param of ty * effect
  | Gen of generalize * t
and t = { v : t' ; loc : Loc.loc }

type decl = 
  | Axiom of string * t
  | Goal of string * t
  | Logic of var *  generalize * ty
  | Section of string * Const.takeover list * decl list
  | TypeDef of generalize * ty option * tyvar
  | Program of var * generalize * t * ParseTypes.t Const.isrec
  | DLetReg of rvar list 
  | DGen of generalize

type theory = decl list

let mk_term v l = { v = v ; loc = l }
let app ?(fix=`Prefix) ?(cap=[]) t1 t2 = 
  mk_term (App (t1,t2,fix, cap))
let var v i = mk_term (Var (v,i))
let svar v = var v Inst.empty

let appi ?(inst=Inst.empty) v t1 t2 loc = 
  app ~fix:`Infix (app (var v inst loc) t1 loc) t2 loc
