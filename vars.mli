open Varsigs

module Name : NAME
type subst'

module TyVar : VARSIG 
   with type subst = subst'
   and type name = Name.t
module Var : VARSIG 
   with type subst = subst'
   and type name = Name.t
type subst = subst'

val eqz_var : Var.t
