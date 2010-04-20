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

type loc = { st : Lexing.position ; en : Lexing.position }
type 'a t = { info:loc ; c : 'a }

val dummy : loc
val mk : loc -> 'a -> 'a t
val mk_pos : Lexing.position -> Lexing.position -> 'a -> 'a t

val strip_info : 'a t list -> 'a list
val embrace : loc -> loc -> loc

val lex_to_lc : Lexing.position -> int * int

val build : Lexing.position -> Lexing.position -> loc
val left_join : Lexing.position -> loc -> loc
val right_join : loc -> Lexing.position -> loc

val join_with : 'a t -> 'a t -> loc
