open Vars

type ('a,'b,'c) t' = 
  | Var of tvar
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c
  | PureArr of 'a * 'a
  | App of tvar * ('a,'b,'c) Inst.t
  | Ref of 'b * 'a
  | Map of 'c
type t = C of (t,rvar,Effect.t) t'

val print : t Myformat.fmt
val print_list : unit Myformat.fmt -> t list Myformat.fmt
val print' : 'a Myformat.fmt -> 'b Myformat.fmt -> 'c Myformat.fmt -> 
              (('a ,'b,'c) t') Myformat.fmt

val var : tvar -> t
val const : Const.ty -> t
val arrow : t -> t -> Effect.t -> t
val parr : t -> t -> t
val tuple : t -> t -> t
val ref_ : rvar -> t -> t
val map : Effect.t -> t
val unit : t
val prop : t
val bool : t
val int : t

val arg : t -> t
val result : t -> t
val latent_effect : t -> Effect.t

val to_logic_type : t -> t

val tlsubst : tvar list -> t list -> t -> t
val rlsubst : rvar list -> rvar list -> t -> t
val app : tvar -> (t,rvar,Effect.t) Inst.t -> t

val equal : t -> t -> bool

module Generalize : sig
  type t = tvar list * rvar list * effvar list

  val empty : t 
  val is_empty : t -> bool

  val print : t Myformat.fmt
end

val allsubst : 
  Generalize.t -> t list * rvar list * Effect.t list -> 
    t -> t

val forty : Generalize.t * t
