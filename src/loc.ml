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

open Lexing

type loc = { st : position ; en : position }
type 'a t = { info:loc ; c : 'a }
let dummy = {st = dummy_pos; en = dummy_pos }

let with_dummy v = { c = v; info = dummy }

let mk i v = { c = v; info =i }

let with_loc f v = { c = f v.c; info = v.info }

let strip_info l = List.map (fun x -> x.c) l

let join x1 x2 =
  {
    st = if x1 = dummy then x2.st else x1.st;
    en = if x2 = dummy then x1.en else x2.en
  }

let build p1 p2 =
  {
    st = p1;
    en = p2
  }

let left_join p x =
  { st = p; en = if x = dummy then p else x.en }

let right_join x p =
  { st = if x = dummy then p else x.st ; en = p }

let lex_to_lc lex =
  let l = lex.pos_lnum in
  let c = lex.pos_cnum - lex.pos_bol in
  l, c

let embrace = join
let mk_pos p1 p2 t = mk (build p1 p2) t

let join_with a1 a2 = join a1.info a2.info
