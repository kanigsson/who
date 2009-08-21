open Vars

exception Error of string * Loc.loc

val form_node : Penv.t -> Formula.t -> Fty.t
(** return the type of a formula wrt an environment, if it is well-typed *)

val allformula: Decl.F.t list -> unit
(** verify that a closed formula is well-typed *)

val is_of_type : Penv.t -> Fty.t -> Formula.t -> unit
(** verify that a formula is of a certain type *)

val check_type : Penv.t -> Fty.t -> Loc.loc -> unit
(** verify wellformedness of the type in an environment *)

val pre_type : Effect.t ->  Fty.t
(** [pre_type eff] returns the type [eff -> prop] *)

val post_type : Effect.t -> Fty.t -> Fty.t
(** [post_type eff t] returns the type [eff -> eff -> t -> prop] *)

