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

exception UndeterminedType

type ty =
  | U
  | Const of Const.ty
  | Tuple of t list
  | Arrow of t * t * rw
  | PureArr of t * t
  | App of Name.t * t list
  | Ref of r * t
  | Map of effect
and t = ty Unionfind.t
and r = rnode Unionfind.t
and rnode =
  | RU
  | RT of Name.t
and effect = r list * Name.S.t
and rw = effect * effect

val eff_empty : effect
val rw_empty : rw
val const : Const.ty -> t
val prop : t
val bool : unit -> t
val int : t
val unit : unit -> t
val parr : t -> t -> t
val arrow : t -> t -> rw -> t
val map : effect -> t

val new_ty : unit -> t

val r_equal : r -> r -> bool

(** conversion functions *)
val from_ty : Ty.t -> t
val from_region : Name.t -> r
val from_effect : Effect.t -> effect
val from_rw : Rw.t -> rw

val to_effect : effect -> Effect.t
val to_rw : rw -> Rw.t
val to_ty : t -> Ty.t
val to_region : r -> Name.t

(* util functions *)

val to_logic_type : t -> t
val nsplit : t -> t list * t
val base_pre_ty : effect -> t
val base_post_ty : effect -> t -> t
val overapprox : rw -> effect

val refresh :
  Ty.Generalize.t -> Effect.t list -> t -> t * (t, r, effect) Inst.t



val rremove : effect -> r list -> effect
val eff_union : effect -> effect -> effect
val eff_union3 : effect -> effect -> effect -> effect
val rw_union : rw -> rw -> rw
val rw_union3 : rw -> rw -> rw -> rw
val rw_rremove : rw -> r list -> rw

val print : t Myformat.fmt
val print_region : r Myformat.fmt
val region_list : r list Myformat.fmt
val print_effect : effect Myformat.fmt
val print_rw : rw Myformat.fmt
