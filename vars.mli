open Name

module Var : NAME
module RVar : NAME
module EffVar : NAME
module TyVar : NAME

val add_var : string -> Var.t -> unit
val get_predef_var : string -> Var.t
