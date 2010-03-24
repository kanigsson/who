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

type ('a,'b,'c) t = 'a list * 'b list * 'c list

val empty : ('a,'b,'c) t

val is_empty : ('a,'b,'c) t -> bool

val equal : 
  ('a -> 'a -> bool) -> ('b -> 'b -> bool) -> ('c -> 'c -> bool) ->
    ('a,'b,'c) t -> ('a,'b,'c) t -> bool

val map : ('a -> 'd) -> ('b -> 'e) -> ('c -> 'f) -> ('a,'b,'c) t -> ('d,'e,'f) t

val iter2 : 
  ('a -> 'd -> unit) -> ('b -> 'e -> unit) -> ('c -> 'f -> unit) ->
    ('a,'b,'c) t -> ('d,'e,'f) t -> unit

val hash : ('a -> int) -> ('b -> int) -> ('c -> int) -> ('a,'b,'c) t -> int

val print : ?kind:[`Who | `Pangoline | `Coq ] -> intype:bool ->
  'a Myformat.fmt -> 'b Myformat.fmt -> 'c Myformat.fmt -> 
      ('a,'b,'c) t Myformat.fmt

