(** the module of Names. Names can be constructed from strings, but names with
 * the same underlying string are not necessarily equal (and aren't if
 * both constructed using [from_string]). *)
type t = private { name : string option ; n : int }
val compare : t -> t -> int
val equal : t -> t -> bool
val new_name : t -> t
val new_anon : unit -> t
val to_string : t -> string
val from_string : string -> t
val print : t Myformat.fmt
val print_list : t list Myformat.fmt

(* binding *)

type subst
(** The type of variable substitutions
 *   it is shared between different variable kinds *)
type 'a bind = subst * t * 'a
(** The type of binding constructs where a single variable is bound *)
type 'a listbind = subst * t list * 'a
(** The type of binding constructs where a list of variables is bound *)


val refresh : subst -> t -> t
(** apply a variable substitution *)
val refresh_bind : subst -> 'a bind -> 'a bind
(** apply a variable substitution to an object under a binder *)

val refresh_listbind : subst -> 'a listbind -> 'a listbind
(** apply a variable substitution to an object under a list binder *)

val open_bind : (subst -> 'a -> 'a) -> 'a bind -> t * 'a
val close_bind : t -> 'a -> 'a bind
(** open / close a binder *)

val open_listbind : (subst -> 'a -> 'a) -> 'a listbind -> t list * 'a
val close_listbind : t list -> 'a -> 'a listbind
(** open / close a list binder *)

val open_with : (subst -> 'a -> 'a) -> t -> 'a bind -> 'a
val list_open_with : (subst -> 'a -> 'a) -> t list -> 'a listbind -> 'a
(** open / close a binder or list binder, but give the fresh variables to use *)


module M : Map.S with type key = t
module S : Set.S with type elt = t
module BMap : MyMap.S with type key = t
module BSet : MySet.S with type elt = t

val print_set : S.t Myformat.fmt
val reset : unit -> unit

