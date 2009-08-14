open Vars

type ('a,'b,'c) t' = 
  | Var of tvar
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c
  | PureArr of 'a * 'a
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

val arg : t -> t

val subst : tvar -> t -> t -> t
val rsubst : rvar -> rvar -> t -> t
val lsubst : tvar list -> t list -> t -> t
val rlsubst : rvar list -> rvar list -> t -> t

val allsubst : 
  Generalize.t -> t list * rvar list * Effect.t list -> 
    t -> t

val equal : t -> t -> bool
