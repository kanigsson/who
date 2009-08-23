open Loc

type t' = 
  | Name of Name.t * (Fty.t, Name.t, Effect.t) Inst.t
  | Const of Const.t
  | App of t * t * [`Infix | `Prefix ]
  | Binder of [ `FA | `EX | `LAM ] *  Fty.t * varbind
  | Gen of letbind
  | PolyLet of letbind * varbind
  | Let of t * varbind
  | Restrict of Effect.t * t
  | Combine of t * t
  | Get of Name.t * t
  | Set of Name.t * t * t
  | Empty
and varbind = t Name.bind
and letbind = t Fty.Generalize.bind
and generalize = Fty.Generalize.t
and t = { v : t'; t : Fty.t ; hint : string option ; loc : Loc.loc }

val lmk : Fty.t -> t' -> Loc.loc -> t
val get_sub : t -> t'
(** access the actual underlying formula, without location and typing
 * information *)
val get_type : t -> Fty.t
val set_type : Fty.t -> t -> t

val print : t Myformat.fmt
val print_node : t' Myformat.fmt
val print_head : t Myformat.fmt

val effsubst : Name.t -> Effect.t -> t -> t
(** effect substitution: [effsubst e eff' f] replaces the effect variable [e]
 * by the effect [eff'] in [f]. Raises [IncompatibleSubst] if an non-disjoint
 * union is attempted *)

val leffsubst : Name.t list -> Effect.t list -> t -> t
(** substitution of a list of effect variables for a list of effects *)

val open_bind : varbind -> Name.t * t
(** open a variable binder *)
val open_bind_with : Name.t -> t Name.bind -> t

val close_bind : Name.t -> t -> varbind
(** close a variable binder *)

val open_tygen : t Name.listbind -> Name.t list * t
val open_tygen_with : Name.t list -> t Name.listbind -> t
val close_tygen : Name.t list -> t -> t Name.listbind
(** open and close a type generalization *)

val open_rbind : t Name.listbind -> Name.t list * t
val open_rbind_with : Name.t list -> t Name.listbind -> t
val close_rbind : Name.t list -> t -> t Name.listbind
(** open and close a reference generalization *)

val open_evgen : t Name.listbind -> Name.t list * t
val open_evgen_with : Name.t list -> t Name.listbind -> t
val close_evgen : Name.t list -> t -> t Name.listbind
(** open and close an effect generalization *)

val open_letgen : letbind -> generalize * t
val open_letgen_with : generalize -> letbind -> t
val close_letgen : generalize -> t -> letbind
(** open and close an let generalized term *)

val with_rec : (t' ->t') -> t -> t
(** modify a formula under its annotations *)

(** smart constructors - do some very simple simplifications *)
val void : loc -> t
val one : loc -> t
val var : Name.t -> (Fty.t, Name.t, Effect.t) Inst.t -> Fty.t -> loc -> t
val svar : Name.t -> Fty.t -> loc -> t
val const : Const.t -> loc -> t
val tuple : t -> t -> loc -> t
val app : ?kind:[`Infix | `Prefix] -> t -> t -> loc -> t
val applist : t list -> loc -> t
val not_ : t -> loc -> t
val impl : t -> t -> loc -> t
val and_ : t -> t -> loc -> t
val andlist : t list -> loc -> t
val eq : t -> t -> loc -> t
val pre : t -> loc -> t
val post : t -> loc -> t
val efflam : Name.t -> Effect.t -> t -> loc -> t
val efflamho : ?name:string -> Effect.t -> (t -> t) -> loc -> t
val effFA : Name.t -> Effect.t -> t -> loc -> t
val effFAho : ?name:string -> Effect.t -> (t -> t) -> loc -> t
val map_empty : loc -> t
val get : Name.t -> t -> Fty.t -> loc -> t
val set : Name.t -> t -> t -> loc -> t
val combine : t -> t -> loc -> t
val restrict : Effect.t -> t -> loc ->  t
val forall : Name.t -> Fty.t -> t -> loc -> t
val forallho : ?name:string -> Fty.t -> (t -> t) -> loc -> t
val gen : Fty.Generalize.t -> t -> loc -> t
val rgen : Name.t list -> t -> loc ->  t
val lam : Name.t -> Fty.t -> t -> loc -> t
val lamho : ?name:string -> Fty.t -> (t -> t) -> loc -> t
val true_ : loc -> t
val false_ : loc -> t
val varbind : [ `FA | `EX | `LAM ] -> Name.t -> Fty.t -> t -> loc -> t
val varbindho : ?name:string ->  [ `FA | `EX | `LAM ] -> Fty.t -> (t -> t) -> loc -> t
val evgen : Name.t list -> t -> loc -> t
val tygen : Name.t list -> t -> loc -> t
val polylet_ : generalize -> Name.t -> t -> t -> loc -> t
val let_ : t -> Name.t -> t -> loc -> t
val massbind : [ `FA | `EX | `LAM ] -> (Name.t * Fty.t) list -> t -> loc -> t
val btrue : loc -> t
val bfalse : loc -> t

val preho : Fty.t -> Effect.t -> (t -> t -> t) -> loc -> t
val postho : 
  Fty.t -> Fty.t -> Effect.t -> (t -> t -> t -> t -> t) -> loc -> t

val le : t -> t -> loc -> t
val lt : t -> t -> loc -> t

val subst : Name.t -> (( Fty.t, Name.t, Effect.t) Inst.t -> t') 
               -> t -> t
(** replace a variable (with instantiations) 
 *  by an expression that knows how to deal with these instantiations *)

val polsubst : Fty.Generalize.t -> Name.t -> t -> t -> t
(** the polymorphic substitution *)

module LocImplicit : sig
  (** "monadic" interface where a single location is passed at the end of the
   * formula construction. More convenient to build large formulas. *)
  type t' = Loc.loc -> t

  val effFA : Name.t -> Effect.t -> t' -> t'
  val effFAho : ?name:string -> Effect.t -> (t' -> t') -> t'
  val efflam : Name.t -> Effect.t -> t' -> t'
  val efflamho : ?name:string -> Effect.t -> (t' -> t') -> t'
  val forall : Name.t -> Fty.t -> t' -> t'
  val forallho : ?name:string -> Fty.t -> (t' -> t') -> t'
  val lam : Name.t -> Fty.t -> t' -> t'
  val lamho : ?name:string -> Fty.t -> (t' -> t') -> t'
  val lamho2 : Fty.t -> Fty.t -> (t' -> t' -> t') -> t'
  val lamho3 : ?name1:string -> ?name2:string -> ?name3:string ->
     Fty.t -> Fty.t -> Fty.t -> (t' -> t' -> t' -> t') -> t'
  val preho : Fty.t -> Effect.t -> (t' -> t' -> t') -> t'
  val postho : 
    Fty.t -> Fty.t -> Effect.t -> (t' -> t' -> t' -> t' -> t') -> t'
  val true_ : t'
  val void : t'
  val eq : t' -> t' -> t'
  val app : t' -> t' -> t'
  val tuple : t' -> t' -> t'
  val impl : t' -> t' -> t'
  val and_ : t' -> t' -> t'
  val applist : t' list -> t'
  val andlist : t' list -> t'
  val pre : t' -> t'
  val post : t' -> t'
  val polylet_ : generalize -> Name.t -> t' -> t' -> t'
  val let_ : t' -> Name.t ->  t' -> t'
  val evgen : Name.t list -> t' -> t'
  val get : Name.t -> t' -> Fty.t -> t'
  val set : Name.t -> t' -> t' -> t'
  val combine : t' -> t' -> t'
  val restrict : Effect.t -> t' -> t'
  val rgen : Name.t list -> t' -> t'
  val tygen : Name.t list -> t' -> t'
  val var : Name.t -> ( Fty.t,  Name.t, Effect.t) Inst.t -> Fty.t -> t'
  val svar : Name.t -> Fty.t ->  t'
  val btrue : t'
  val bfalse : t'
  val le : t' -> t' -> t'
  val encl : t' -> t' -> t' -> t'
  val succ : t' -> t'
  val max :  t' -> t' -> t'
  val min :  t' -> t' -> t'
  val prev : t' -> t'
  val subst : Name.t -> ((Fty.t,  Name.t, Effect.t) Inst.t -> t') -> t' -> t'
end

val domain : t -> Effect.t

val destruct_infix : t -> (Name.t * t * t) option
val destruct_infix' : t' -> (Name.t * t * t) option
