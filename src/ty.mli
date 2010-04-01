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

type t =
  | Const of Const.ty
  | Tuple of t list
  | Arrow of t * t * Rw.t * Name.t list
  | PureArr of t * t
  | App of Name.t * inst
  | Ref of Name.t * t
  | Map of Effect.t
and inst = t list

val print : t Myformat.fmt
val print_list : unit Myformat.fmt -> t list Myformat.fmt
val coq_print : t Myformat.fmt
val gen_print : ?kind:[`Coq | `Who | `Pangoline ] -> t Myformat.fmt

val var : Name.t -> t
val const : Const.ty -> t
val arrow : t -> t -> Rw.t -> t
val caparrow : t -> t -> Rw.t -> Name.t list -> t
val parr : t -> t -> t
val tuple : t list -> t
val ref_ : Name.t -> t -> t
val map : Effect.t -> t
val unit : unit -> t
val prop : t
val bool : unit -> t

val region : t -> t
val refty : t -> t -> t
val int : t
val emptymap : t

val is_unit : t -> bool
val arg : t -> t
val result : t -> t
val split : t -> t * t
val nsplit : t -> t list * t
val latent_effect : t -> Rw.t
val domain : t -> Effect.t
val is_map : t -> bool
val is_ref : t -> bool
val destr_ref : t -> t
val destr_pair : t -> t * t
val tuple_arity : t -> int
val tuple_list : t -> t list

val node_map :
    ?rfun:(Name.t -> Name.t) ->
    ?effectfun:(Effect.t -> Effect.t) -> (t -> t) -> t -> t

val to_logic_type : t -> t
val from_logic_pair : t -> t * t * Effect.t

val tlsubst : Name.t list -> t list -> t -> t
val rlsubst : Name.t list -> Name.t list -> t -> t
val elsubst : Name.t list -> Effect.t list -> t -> t
val rsubst : Name.t list -> Name.t list -> Name.t -> Name.t
val app : Name.t -> t list -> t

val equal : t -> t -> bool

module Generalize : sig
  type t = Name.t list * Name.t list * Name.t list
  type 'a bind = 'a Name.listbind Name.listbind Name.listbind

  val empty : t
  val is_empty : t -> bool

  val print : t Myformat.fmt
  val open_ : (Name.subst -> 'a -> 'a) -> 'a bind -> t * 'a
  val sopen_ : 'a bind -> t * 'a
  val close : t -> 'a -> 'a bind

  val equal : t -> t -> bool

end

type scheme = Generalize.t * t

val print_scheme : scheme Myformat.fmt

val allsubst :
  Generalize.t -> t list * Name.t list * Effect.t list ->
    t -> t

val find_type_of_r : Name.t -> t -> t option

val get_reg : t -> Name.t

val selim_map : (Name.t -> t) -> t -> t

val base_pretype : Effect.t -> t
val base_posttype : t -> Rw.t -> t
val pretype : t -> Effect.t -> t
val posttype : t -> t -> Rw.t -> t
val prepost_type: t -> t -> Rw.t -> t

val matching : Name.S.t -> t Name.M.t -> t -> t -> t Name.M.t

module Convert : sig
  val t : Name.Env.t -> t -> PrintTree.ty
  val scheme : Name.Env.t -> scheme -> PrintTree.scheme
  val gen : Name.Env.t -> Generalize.t -> Name.Env.t * PrintTree.gen
end
