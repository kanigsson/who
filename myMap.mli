module type S = 
sig
  type key
  type 'a t = (key * 'a) list

  val empty : 'a t
  val is_empty : 'a t -> bool
  val domain : 'a t -> key list
  val restrict : 'a t -> key list -> 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val map : ('a -> 'b) -> 'a t -> 'b t
  val add : key -> 'a -> 'a t -> 'a t
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold_up : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val compose : 'a t -> 'a t -> 'a t
  val canon : 'a t -> 'a t
  val print : 
    (Format.formatter -> unit -> unit) -> 
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a t -> unit
end
