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
val not_id : string
val restrict_id : string

val fst_id : string
val snd_id : string

val plus_id : string
val minus_id : string

val mk_tuple_id : int -> string
val get_tuple_id  : int -> int -> string
val refget_id : string

val ref_id : string

val unsafe_equal : Name.t -> string -> bool

val is_infix_id : string -> bool

val infix_ids : string list
val effect_ids : string list
