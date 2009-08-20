module type S = sig
  type elt
  type t = elt list

  val empty : t
  val is_empty : t -> bool
  val singleton : elt -> t
  val mem : elt ->  t -> bool
  val add : elt ->  t -> t
  val remove : elt -> t -> t
  val union : t -> t -> t
  val intersection : t -> t -> t
  val compare : t -> t -> int
  val are_disjoint : t -> t -> bool
  val canon : t -> t
  val fold : (elt -> 'a -> 'a) -> t ->'a -> 'a
  val map : (elt -> elt) -> t -> t
  val iter : (elt -> unit) -> t -> unit
  val print : (Format.formatter -> unit -> unit) -> Format.formatter -> 
                 t -> unit
end

module type CanonType = sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end
