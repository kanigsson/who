type effect = string list * string list
type rw = effect * effect
type ty =
  | TConst of Const.ty
  | Tuple of ty list
  | Arrow of ty * ty * rw
  | PureArr of ty * ty
  | TApp of string * ty list
  | Ref of string * ty
  | Map of effect

type inst = ty list * string list * effect list
type gen = string list * string list * string list
type scheme = gen * ty

type t =
  | Const of Const.t
  | Var of string * inst * ty * [`Infix | `Prefix ]
  | Get of t * t
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t
  | Lam of string * ty * funcbody
  | Let of gen * t * string * t * isrec
  | PureFun of string * ty * t
  | Ite of t * t * t
  | Quant of [`FA | `EX ] * string * ty * t
  | Param of ty * rw
  | Gen of gen *  t
  | PRef of string
  | HoareTriple of funcbody
  | LetReg of string list * t
  | Case of t * branch list
  | SubEff of t * ty * rw
and funcbody = t * t * t
and isrec = ty Const.isrec
and branch = pattern * t
and pattern =
  | PVar of string
  | PApp of string * inst * pattern list

type decl =
  | Logic of string * scheme
  | Formula of string * t * [ `Proved | `Assumed ]
  | Section of string * decl list * section_kind
  | TypeDef of string * string list * typedef
  | Inductive of string * gen * ty list * inductive_branch list
  | Program of string * gen * t * isrec
  | DLetReg of string list
  | DGen of gen
  | Decl of string
and typedef =
  | Abstract
  | ADT of constbranch list
and constbranch = string * ty list
and inductive_branch = string * t

and section_kind = [ `Block of Const.takeover list | `Structure ]
and theory = decl list

module Print : sig
  val term : ?kind:Const.prover -> t Myformat.fmt
  val decl : ?kind:Const.prover -> decl Myformat.fmt
  val theory : ?kind:Const.prover -> theory Myformat.fmt

  val effect_no_sep : effect Myformat.fmt
  val effect : effect Myformat.fmt
  val rw : rw Myformat.fmt
  val ty : ?kind:Const.prover -> ty Myformat.fmt
  val scheme : scheme Myformat.fmt
  val gen : gen Myformat.fmt
end
