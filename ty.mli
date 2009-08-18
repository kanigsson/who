open Vars

type ('a,'b,'c) t' = 
  | Var of TyVar.t
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c
  | PureArr of 'a * 'a
  | App of TyVar.t * ('a,'b,'c) Inst.t
  | Ref of 'b * 'a
  | Map of 'c
type t = C of (t,RVar.t,Effect.t) t'

val print : t Myformat.fmt
val print_list : unit Myformat.fmt -> t list Myformat.fmt
val print' : 'a Myformat.fmt -> 'b Myformat.fmt -> 'c Myformat.fmt -> 
              ('a -> bool) -> (('a ,'b,'c) t') Myformat.fmt

val is_compound : ('a,'b,'c) t' -> bool
val var : TyVar.t -> t
val const : Const.ty -> t
val arrow : t -> t -> Effect.t -> t
val caparrow : t -> t -> Effect.t -> RVar.t list -> t
val parr : t -> t -> t
val tuple : t -> t -> t
val ref_ : RVar.t -> t -> t
val map : Effect.t -> t
val unit : t
val prop : t
val bool : t
val int : t

val arg : t -> t
val result : t -> t
val latent_effect : t -> Effect.t

val to_logic_type : t -> t

val tlsubst : TyVar.t list -> t list -> t -> t
val rlsubst : RVar.t list -> RVar.t list -> t -> t
val app : TyVar.t -> (t,RVar.t,Effect.t) Inst.t -> t

val equal : t -> t -> bool

module Generalize : sig
  type t = TyVar.t list * RVar.t list * EffVar.t list

  val empty : t 
  val is_empty : t -> bool

  val print : t Myformat.fmt
end

val allsubst : 
  Generalize.t -> t list * RVar.t list * Effect.t list -> 
    t -> t

val forty : Generalize.t * t
