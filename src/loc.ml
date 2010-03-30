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

type loc = {st: int * int; en: int * int}
type 'a t = { info:loc ; c : 'a }
let dummy = {st = (0,0); en = (0,0) }

let with_dummy v = { c = v; info = dummy }

let mk i v = { c = v; info =i }

let with_loc f v = { c = f v.c; info = v.info }

let strip_info l = List.map (fun x -> x.c) l

let embrace inf1 inf2 =
  if inf1 = dummy then inf2
  else if inf2 = dummy then inf1
  else { st = inf1.st ; en = inf2.en }

