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

val equal : t -> t -> bool
val empty : t
val is_empty : t -> bool

val reads : t -> Effect.t
val writes : t -> Effect.t
val reads_only : t -> Effect.t
val read_write : t -> Effect.t * Effect.t

val mk : read:Effect.t -> write:Effect.t -> t
val map : (Effect.t -> Effect.t) -> t -> t

val union : t -> t -> t
val union3 : t -> t -> t -> t
val rremove : t -> Name.t list -> t


val overapprox : t -> Effect.t
val kernel : t -> Effect.t

module Convert : sig
  val t : Name.Env.t -> t -> PrintTree.rw
end

val print : t Myformat.fmt
