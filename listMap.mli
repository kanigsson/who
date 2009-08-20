(* A map that only needs equality on keys *)
module Make : functor (O : MySet.CanonType) -> 
  MyMap.S with type key = O.t
