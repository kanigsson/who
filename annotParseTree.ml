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
  | Lam of var * ty * rvar list * pre * t *  post 
  (* boolean which describes if the let comes from the prelude or not *)  
  | Let of generalize * t * var * t * isrec
  | PureFun of ty * var * t
  | Ite of t * t * t
  | Annot of t * ty
  | Quant of [`FA | `EX ] * ty * var * t
  | Param of ty * effect
  | Gen of generalize * t
and t = { v : t' ; loc : Loc.loc }
and isrec = Rec of ty | NoRec
and pre = var * t
and post = var * var * var * t

type decl = 
  | Axiom of string * t
  | Logic of var *  generalize * ty
  | Section of string * Const.takeover list * decl list
  | TypeDef of generalize * ty option * tyvar
  | Program of var * generalize * t
  | LetReg of rvar list 

type theory = decl list
