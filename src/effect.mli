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

type t

val empty : t
val is_empty : t -> bool
val no_effvar : t -> bool

val esingleton : Name.t -> t
val is_esingleton : t -> bool
val e_choose : t -> Name.t

val rmem : t -> Name.t -> bool
val emem : t -> Name.t -> bool

val to_lists : t -> Name.t list * Name.t list
val to_rlist : t -> Name.t list
val to_elist : t -> Name.t list
val from_lists : Name.t list -> Name.t list -> t
val from_u_effect : Name.t list -> Name.S.t -> t
val to_u_effect : t -> Name.t list * Name.S.t

val eadd :  t -> Name.t -> t
val radd :  t -> Name.t -> t
val rremove : t -> Name.t list -> t
val eremove : t -> Name.t -> t
val print : t Myformat.fmt
val print_nosep: t Myformat.fmt
val union : t -> t -> t
val union3 : t -> t -> t -> t
val equal : t -> t -> bool
val rmap : (Name.t -> Name.t) -> t -> t
val lsubst : Name.t list -> t list -> t -> t
val rfold : (Name.t -> 'a -> 'a) -> 'a -> t -> 'a
val efold : (Name.t -> 'a -> 'a) -> 'a -> t -> 'a
val eiter : (Name.t -> unit) -> t -> unit
val inter : t -> t -> t
val diff : t -> t -> t

val sub_effect : t -> t -> bool

val split : t -> t -> t * t * t
(** take two effects and return:
    * the first without the second
    * their intersection
    * the second without the first
*)

val s_equal : Name.S.t -> Name.S.t -> bool
