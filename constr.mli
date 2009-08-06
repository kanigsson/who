open Vars

type t = 
  | True
  | Sub of Var.t * Ty.t
  | Eq of Ty.t * Ty.t
  | And of t * t
  | Exists of t TyVar.listbind
  | Let of constr_scheme * t Var.bind
and constr_scheme = (Ty.t * t) TyVar.listbind

val print : t Misc.fmt

val open_bind : t Var.bind -> Var.t * t
val close_bind : Var.t -> t -> t Var.bind 
val open_tybind : t TyVar.listbind -> TyVar.t list * t
val close_tybind : TyVar.t list -> t -> t TyVar.listbind

val open_scheme : constr_scheme -> TyVar.t list * (Ty.t * t)

val exists : (Ty.t -> t) -> t
val exists2 : (Ty.t -> Ty.t -> t) -> t

val let_ : constr_scheme -> Var.t -> t -> t
val true_ : t

val triv_scheme : Ty.t -> constr_scheme

val mk_scheme : (Ty.t -> Ty.t * t) -> constr_scheme
