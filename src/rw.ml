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
  (* We incode the invariant write \subseteq read by saying that [read] contains
   * only the effects that are not already contained in [write]. *)
  {
    read : Effect.t ;
    write : Effect.t
  }

let mk ~read ~write =
  { write = write; read = Effect.diff read write }

let reads a = Effect.union a.read a.write
let writes a = a.write
let reads_only a = a.read

let read_write a = reads a, writes a

let map f e =
  { read = f e.read ; write = f e.write }

let empty = { read = Effect.empty; write = Effect.empty }

let equal e1 e2 =
  Effect.equal e1.read e2.read && Effect.equal e1.write e2.write

let is_empty rw =
  Effect.is_empty rw.read && Effect.is_empty rw.write

let union e1 e2 =
  mk ~read:(Effect.union e1.read e2.read)
    ~write:(Effect.union e1.write e2.write)

let union3 a b c = union a (union b c)

let rremove e rl = map (fun e -> Effect.rremove e rl) e
let overapprox e = reads e

let kernel e = e.write

module Convert = struct
  let t env e =
    Effect.Convert.t env e.read, Effect.Convert.t env e.write
end

module Print = struct
  open PrintTree

  let emp = Name.Env.empty Name.M.empty
  let rw fmt e = Print.rw fmt (Convert.t emp e)
end

let print = Print.rw

let sub a b =
  Effect.sub_effect a.read b.read && Effect.sub_effect a.write b.write
