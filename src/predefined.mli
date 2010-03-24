module Identifier : sig
  val empty_id : string
  val btrue_id : string
  val bfalse_id : string
  val void_id : string
  val leb_id  : string
  val ltb_id  : string
  val geb_id  : string
  val gtb_id  : string
  val eqb_id  : string
  val neqb_id : string
  val andb_id : string
  val orb_id  : string
  val le_id : string
  val lt_id : string
  val ge_id : string
  val gt_id : string
  val equal_id : string
  val neq_id : string
  val or_id : string
  val and_id : string
  val impl_id : string
  val combine_id : string
  val get_id : string
  val fst_id : string
  val snd_id : string
  val not_id : string
  val restrict_id : string
  
  val plus_id : string
  val minus_id : string

  val mk_tuple_id : int -> string

  val unsafe_equal : Name.t -> string -> bool
end

module Logic : sig 

  val get_pangoline_id : Name.t -> string
  val var_and_type : string -> Name.t * (Ty.Generalize.t * Ty.t)

  val equal : Name.t -> string -> bool
  
  val init : (Ty.Generalize.t * Ty.t) Name.M.t -> unit

  val belongs_to : Name.t -> string list -> bool
end
