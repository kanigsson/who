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
  val print : t Myformat.fmt
  val print_list : t list Myformat.fmt

  module M : Map.S with type key = t
  module S : Set.S with type elt = t

  val print_set : S.t Myformat.fmt
end

module Name : NAME
