type t' =
  | Const of Const.t
  | Var of Name.t * (MutableType.t,MutableType.r, MutableType.effect) Inst.t
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t * [`Infix | `Prefix ] * Name.t list
  | Lam of Name.t * Ty.t * Name.t list * funcbody
  | Let of Ty.Generalize.t * t * t Name.bind * isrec
  | PureFun of MutableType.t * t Name.bind
  | Ite of t * t * t
  | Annot of t * Ty.t
  | Quant of [`FA | `EX ] * MutableType.t * t Name.bind
  | Param of Ty.t * Effect.t
  | Gen of Ty.Generalize.t * t
  | For of Name.t * pre * Name.t * Name.t * Name.t * t
  | HoareTriple of funcbody
  | LetReg of Name.t list * t
and t = { v : t' ; t : MutableType.t ;
          e : MutableType.effect ; loc : Loc.loc }
and post = t
and pre = t
and isrec = Ty.t Const.isrec
and funcbody = pre * t * post

type decl =
  | Logic of Name.t * Ty.Generalize.t * Ty.t
  | Formula of string * t * [ `Proved | `Assumed ]
  | Section of string * Const.takeover list * decl list
  | TypeDef of Ty.Generalize.t * Ty.t option * Name.t
  | Program of Name.t * Ty.Generalize.t * t * isrec
  | DLetReg of Name.t list
  | DGen of Ty.Generalize.t

type theory = decl list

val pure_lam : Name.t -> MutableType.t -> t -> Loc.loc -> t
