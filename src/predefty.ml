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

type error =
  | PreludeIncomplete of string

exception Error of error

let error e = raise (Error e)

let explain error =
  match error with
  | PreludeIncomplete s ->
      Myformat.sprintf "the prelude is incomplete; the following symbol is \
        missing: %s" s

module Identifier = struct
  let bool_id = "bool"
  let unit_id = "unit"
  let region_id = "region"
end

type env = Name.t Misc.StringMap.t ref

let env = ref Misc.StringMap.empty
let add_symbol s x = env := Misc.StringMap.add s x !env
let base_var s = Misc.StringMap.find s !env
let var s =
  try base_var s
  with Not_found -> error (PreludeIncomplete s)

let equal x id =
  try
    let y = base_var id in
    Name.equal x y
  with Not_found -> false
