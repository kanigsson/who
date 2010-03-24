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

type 'a t = 'a list
type 'a eq = 'a -> 'a -> bool

val equal : 'a eq -> 'a t -> 'a t -> bool
val mem : 'a eq -> 'a -> 'a t -> bool


val union : 'a eq -> 'a t -> 'a t -> 'a t
val equal_unsorted : 'a eq -> 'a t -> 'a t -> bool

val fold_map : ('a  -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list

val hash : ('a -> int) -> int -> 'a list -> int
