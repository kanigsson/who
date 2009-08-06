module type NAME =
sig
  (** the module of Names. Names can be constructed from strings, but names with
   * the same underlying string are not necessarily equal (and aren't if
   * both constructed using [from_string]). *)
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val new_name : t -> t
  val new_anon : unit -> t
  val to_string : t -> string
  val from_string : string -> t
  val print : Format.formatter -> t -> unit
end

module type VARSIG =
sig
  (** The common signature of all variables kinds *)

  type t
  (** The type of a variable *)

  type name
  (** The type of names - it is shared between variable kinds *)

  type 'a bind
  (** The type of binding constructs where a single variable is bound *)
  type 'a listbind
  (** The type of binding constructs where a list of variables is bound *)

  type subst
  (** The type of variable substitutions
   *   it is shared between different variable kinds *)

  val refresh : subst -> t -> t
  (** apply a variable substitution *)
  val refresh_bind : subst -> 'a bind -> 'a bind
  (** apply a variable substitution to an object under a binder *)

  val refresh_listbind : subst -> 'a listbind -> 'a listbind
  (** apply a variable substitution to an object under a list binder *)

  val deb_open : 'a bind -> t * 'a
  (** open a binder without refreshing *)

  val deb_listopen : 'a listbind -> t list * 'a
  (** open a list binder without refreshing *)

  val open_bind : (subst -> 'a -> 'a) -> 'a bind -> t * 'a
  val close_bind : t -> 'a -> 'a bind
  (** open / close a binder *)

  val open_listbind : (subst -> 'a -> 'a) -> 'a listbind -> t list * 'a
  val close_listbind : t list -> 'a -> 'a listbind
  (** open / close a list binder *)

  val open_with : (subst -> 'a -> 'a) -> t -> 'a bind -> 'a
  val list_open_with : (subst -> 'a -> 'a) -> t list -> 'a listbind -> 'a
  (** open / close a binder or list binder, but give the fresh variables to use *)

  val compare : t -> t -> int
  val equal : t -> t -> bool
  (** comparison and equality *)

  val from_string : string -> t
  val new_name : t -> t
  val new_from_name : name -> t
  val new_anon : unit -> t
  val to_name : t -> name
  (** constructors and accessors *)

  val to_string : t -> string
  (** [to_string x] returns a string which is unique for this variable. It
   * should only be called once per variable. *)

  val reset : unit -> unit
  (** permits to reset the uniqueness information used in [to_string] *)

  module FreeMap : Map.S with type key = t
  module FreeSet : Set.S with type elt = t
  val print : Format.formatter -> t -> unit
  val print_list : Format.formatter -> t list -> unit
end
