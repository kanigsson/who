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

(** the module of Names. Names can be constructed from strings, but names with
 * the same underlying string are not necessarily equal (and aren't if
 * both constructed using [from_string]). *)
type t = private { name : string option ; n : int }
val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int
val new_name : t -> t
val new_anon : unit -> t
val to_string : t -> string
val unsafe_to_string : t -> string
val from_string : string -> t
val print : t Myformat.fmt
val print_list : t list Myformat.fmt

(* binding *)

type subst
(** The type of variable substitutions
 *   it is shared between different variable kinds *)
type 'a bind = subst * t * 'a
(** The type of binding constructs where a single variable is bound *)
type 'a listbind = subst * t list * 'a
(** The type of binding constructs where a list of variables is bound *)


val refresh : subst -> t -> t
(** apply a variable substitution *)
val refresh_bind : subst -> 'a bind -> 'a bind
(** apply a variable substitution to an object under a binder *)

val refresh_listbind : subst -> 'a listbind -> 'a listbind
(** apply a variable substitution to an object under a list binder *)

val open_bind : (subst -> 'a -> 'a) -> 'a bind -> t * 'a
val sopen : (subst -> 'a -> 'a) -> 'a bind -> t * 'a
val close_bind : t -> 'a -> 'a bind
(** open / close a binder *)

val open_listbind : (subst -> 'a -> 'a) -> 'a listbind -> t list * 'a
val close_listbind : t list -> 'a -> 'a listbind
(** open / close a list binder *)

val open_with : (subst -> 'a -> 'a) -> t -> 'a bind -> 'a
val list_open_with : (subst -> 'a -> 'a) -> t list -> 'a listbind -> 'a
(** open / close a binder or list binder, but give the fresh variables to use *)


module M : Map.S with type key = t
module S : Set.S with type elt = t
module H : Hashtbl.S with type key = t
val print_set : S.t Myformat.fmt

val hash_set : S.t -> int

val reset : unit -> unit

val list_to_set : t list -> S.t
val set_to_list : S.t -> t list

val remove_list_from_set : t list -> S.t -> S.t
