open Varsigs

type subst'

module TyVar : VARSIG 
   with type subst = subst'
   and type name = Name.t
module Var : VARSIG 
   with type subst = subst'
   and type name = Name.t
module RVar : VARSIG 
   with type subst = subst'
   and type name = Name.t
module EffVar : VARSIG 
   with type subst = subst'
   and type name = Name.t

type subst = subst'

val init : unit -> unit
val get_predef_var : string -> Var.t

(*
val lookup_var : Var.t
val assign_var : Var.t
val ref_var : Var.t
val map_combine_var : Var.t
val map_restrict_var : Var.t
val map_set_var : Var.t
val map_empty_var : Var.t
val set_add_var : Var.t
val set_union_var : Var.t
val set_empty_var : Var.t
val domain_var : Var.t
val plus_var : Var.t
val minus_var : Var.t
val mult_var : Var.t
val le_var : Var.t
val leb_var : Var.t
val eqz_var : Var.t
val lt_var : Var.t
val ltb_var : Var.t
val max_var : Var.t
val min_var : Var.t
val for_var_to : Var.t
val for_var_downto : Var.t
val and_var : Var.t
val impl_var: Var.t
val eqvar : Var.t
val mk_tuple_var : Var.t
val fst_var : Var.t
val snd_var : Var.t
val neg_var : Var.t
*)
