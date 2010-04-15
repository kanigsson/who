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

open Myformat
open Lexing

let bad s = eprintf "%s@." s; exit(1)

let error fn l c s =
  let fn = Opt.get "stdin" fn in
  eprintf "%s: line %d char %d : %s @." fn l c s

let print_pos_error fn buf s =
  let p = buf.lex_curr_p in
  let l = p.pos_lnum in
  let c = p.pos_cnum - p.pos_bol in
    error fn l c s

let with_loc msg {Loc.st = (sta,stb); en = _} =
  error !Options.filename sta stb msg; exit(1)
