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

module Env : sig
  type t
  val empty : t

  val rlookup : t -> Name.t -> Ty.t
  val elookup : t -> Name.t -> Ty.t
end = struct

  module M = Name.M
  type t =
    { r : Ty.t M.t ; e : Ty.t M.t }

  let empty =
    { r = M.empty ; e = M.empty }

  let rlookup env t = M.find t env.r
  let elookup env t = M.find t env.e

end

open Ast
open Recon

let effect_to_tuple_type env eff =
  let rl,el = Effect.to_lists eff in
  let rt = List.map (Env.rlookup env) rl in
  let et = List.map (Env.elookup env) el in
  Ty.tuple (rt@et)

