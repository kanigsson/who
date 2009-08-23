type t
(** The type of effects *)

exception IncompatibleSubst

val empty : t
(** The empty effect *)

val is_empty : t -> bool
(** Returns true when the effect is empty *)

val esingleton : Name.t -> t
(** [esingleton e] returns the effect that contains only the effect var [e] *)

val emem : Name.t -> t -> bool
(** Presence test for effect variables  *)

val eadd : Name.t -> t -> t
(** add one effect var to the effect  *)

val radd : Name.t -> t -> t
(** add one reference to the effect  *)

val rsingleton : Name.t -> t
(** [rsingleton r] returns the effect that contains only the reference [r] *)

val rmem : Name.t -> t -> bool
(** Presence test for references  *)

val from_sets : Name.BSet.t -> Name.BSet.t -> t
(** build the effect that corresponds to the union of a set of references and
 * a set of effect vars  *)

val to_sets : t -> Name.BSet.t * Name.BSet.t
(** the inverse of [from_sets]  *)

val fold : (Name.t -> 'a -> 'a) -> (Name.t -> 'a -> 'a) -> t -> 'a -> 'a
(** fold over the effect, while preserving the order of the elements *)

val efold : (Name.t -> 'a -> 'a) -> t -> 'a -> 'a
val rfold : (Name.t -> 'a -> 'a) -> t -> 'a -> 'a

val canon : t -> t
(** Put the effect in canonical representation *)

val union : t -> t -> t
(** union of effects *)

val minus : t -> t -> t
(** Set difference of effects *)

val are_disjoint : t -> t -> bool
(** test for disjointness *)

val disjoint_union : t -> t -> t
(** disjoint union, raises [IncompatibleSubst] if arguments are not disjoint *)

val intersection : t -> t -> t
(** intersection of effects *)

val refresh : Name.subst -> t -> t
(** apply a variable substitution to an effect *)

val is_subset : t -> t -> bool

val compare : t -> t -> int
(** comparison function *)

val equal : t -> t -> bool
(** equality test *)

val print : t Myformat.fmt
val print_list : t list Myformat.fmt

val effsubst : Name.t -> t -> t -> t
(** effect substitution: [effsubst e eff' eff] replaces the effect variable [e]
 * by the effect [eff'] in [eff]. Raises [IncompatibleSubst] if an non-disjoint
 * union is attempted *)

val rsubst : Name.t -> Name.t -> t -> t

val explode : t -> t list
(** transform the effect in a list of singleton effects *)

val rremove : Name.t -> t -> t

val free_rvars : t -> Name.S.t
