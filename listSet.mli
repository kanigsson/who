(** A set that only needs equality on elements *)
module Make : functor (O : MySet.CanonType) -> MySet.S with type elt = O.t
