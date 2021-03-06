(******************************************************************************)
(*                                                                            *)
(*                      Who                                                   *)
(*                                                                            *)
(*       A simple VCGen for higher-order programs.                            *)
(*                                                                            *)
(*  Copyright (C) 2009, 2010, Johannes Kanig                                  *)
(*  Contact: kanig@lri.fr                                                     *)
(*                                                                            *)
(*  Who is free software: you can redistribute it and/or modify it under the  *)
(*  terms of the GNU Lesser General Public License as published by the Free   *)
(*  Software Foundation, either version 3 of the License, or any later        *)
(*  version.                                                                  *)
(*                                                                            *)
(*  Who is distributed in the hope that it will be useful, but WITHOUT ANY    *)
(*  WARRANTY; without even the implied warranty of MERCHANTABILITY or         *)
(*  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public      *)
(*  License for more details.                                                 *)
(*                                                                            *)
(*  You should have received a copy of the GNU Lesser General Public License  *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>      *)
(******************************************************************************)

type error

exception Error of error

val explain : error -> string

type binding = Ty.Generalize.t * Ty.t * [`Infix | `Prefix ]
val var_and_type : string -> Name.t * binding
val var : string -> Name.t

val equal : Name.t -> string -> bool

val add_binding : Name.t -> binding -> unit
val add_symbol : string -> Name.t -> unit
val add_symbol_and_binding :
  string -> Name.t -> binding -> unit

val is_infix : Name.t -> bool
val is_effect_var : Name.t -> bool
val is_get_tuple_var : Name.t -> int option
val is_mk_tuple : Name.t -> bool

val pangoline_map : unit -> string Name.M.t
val coq_map : unit -> string Name.M.t
val why3_map : unit -> string Name.M.t
