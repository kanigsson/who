open Vars

type ('a,'b,'c) t'' = [ ('a,'b) Lty.t'' | `Map of 'c | `Ref of RVar.t * 'a ]
type 'a t' = ('a,TyVar.t,Effect.t) t''
type t = [ `U of t t' ]

val print'': 'a Myformat.fmt -> 'b Myformat.fmt -> 'c Myformat.fmt -> ('a,'b,'c) t'' Myformat.fmt
val print' : 'a Myformat.fmt -> 'a t' Myformat.fmt
val print : t Myformat.fmt
val print_list : t list Myformat.fmt
val binder : (Var.t * t) Myformat.fmt

val map' : 
  ('a -> 'b) -> 
      tyvarfun:(TyVar.t -> ([> 'b t'] as 'd)) -> 
      effectfun:(Effect.t -> Effect.t) ->
      rvarfun:(RVar.t -> RVar.t) ->
        'a t' -> 'd
val map : 
  tyvarfun:(TyVar.t -> t t') -> 
  effectfun:(Effect.t -> Effect.t) -> 
  rvarfun:(RVar.t -> RVar.t) ->
    t -> t

val refresh : subst -> t -> t
(** apply a variable substitution to a logic type *)

(* some predefined type variables *)
val key_var : TyVar.t
val map_var : TyVar.t
val set_var : TyVar.t



(** smart constructors *)
val var : TyVar.t -> t
val arr : t -> t -> t
val app : TyVar.t -> t list -> t
val tuple : t -> t -> t
val mkmap : Effect.t -> t
val maparr : Effect.t -> t -> t
val massarrow : t list -> t -> t

(** smart constants *)
val prop : t
val int : t
val bool : t
val unit : t
val const : Const.ty -> t

(* predefined types *)
val iii : t
val ppp : t
(* int -> int -> int *)
val iip : t
(* int -> int -> prop *)
val iib : t
(* int -> int -> bool *)
val mmm : t
(* map -> map -> map *)
val kvmm : t -> t
(* key -> 'a -> map -> map *)
val smm : t
(* set -> map -> map *)

val kss : t
(* key -> set -> set *)
val sss : t
(* set -> set -> set *)
val ms : t
(* map -> set *)



val compare' : ('a -> 'a -> int) -> 'a t' -> 'a t' -> int
val compare : t -> t -> int
val equal : t -> t -> bool
(** comparison and equality *)

val well_formed' : ('a -> bool) -> (TyVar.t -> int) -> 'a t' -> bool
val well_formed : (TyVar.t -> int) -> t -> bool
(** wellformedness; the argument is a function that returns the arity of a type
 * *)

val effsubst : EffVar.t -> Effect.t -> t -> t
(** effect substitution: [effsubst e eff' t] replaces the effect variable [e]
 * by the effect [eff'] in [t]. Raises [IncompatibleSubst] if an non-disjoint
 * union is attempted *)

val rsubst : RVar.t -> RVar.t -> t -> t

val leffsubst : EffVar.t list -> Effect.t list -> t -> t
(** replace a list of effect variables by a list of effects *)

val tysubst : TyVar.t -> t -> t -> t
(** type substitution: [tysubst alpha tau' t] replaces the type variable
 * alpha * by the type [tau'] in [t]. *)
val ltysubst : TyVar.t list -> t list -> t -> t

module Generalize : sig
  type t =  TyVar.t list * RVar.t list * EffVar.t list
  type 'a bind = 
    'a RVar.listbind TyVar.listbind EffVar.listbind 

  val is_empty : t -> bool
  val empty : t

  val open_bind :
    (Vars.RVar.subst -> 'a -> 'a) -> 'a bind -> t * 'a

  val open_bind_with :
    (Vars.RVar.subst -> 'a -> 'a) -> t -> 'a bind -> 'a

  val close_bind : t -> 'a -> 'a bind

  val print : t Myformat.fmt
end

module Scheme : sig
  (** the module of logic type schemes *)
  type fty = t
  type t
  val fty : fty -> t
  val instance : t -> Effect.t list -> fty list -> RVar.t list -> fty
  (** get the instance of a type scheme wrt. lists of effects and types *)
  val print : t Myformat.fmt

  val open_ : t -> Generalize.t * fty
  val close : Generalize.t -> fty -> t
  (** open and close logic type schemes *)
end

val domain : t -> Effect.t
val arg : t -> t
val result : t -> t
val left : t -> t
val right : t -> t

val to_lty : t -> Lty.t
val ltyf : t -> t

val init : unit -> unit
val get_predef_var : string -> Var.t * TyVar.t list * t

val from_ty : Ty.t -> t
val from_eff : NEffect.t -> Effect.t
