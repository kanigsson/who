type tvar = string
type rvar = string
type effvar = string
type ('a,'b,'c) t' = 
  | Var of string
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c
  | Ref of 'b * 'a
type t = C of (t,rvar,Effect.t) t'

val print : t Misc.fmt
val print' : 'a Misc.fmt -> 'b Misc.fmt -> 'c Misc.fmt -> (('a ,'b,'c) t') Misc.fmt

val var : tvar -> t
val const : Const.ty -> t
val arrow : t -> t -> Effect.t -> t
val tuple : t -> t -> t
val ref_ : rvar -> t -> t
val unit : t

val arg : t -> t

val subst : tvar -> t -> t -> t
val rsubst : rvar -> rvar -> t -> t
val lsubst : tvar list -> t list -> t -> t
val rlsubst : rvar list -> rvar list -> t -> t

val allsubst : 
  tvar list * rvar list * effvar list -> t list * rvar list * Effect.t list -> 
    t -> t

val equal : t -> t -> bool
