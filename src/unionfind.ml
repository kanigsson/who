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

type 'a t = { mutable father : 'a t; mutable rank : int; 
              mutable desc : 'a; tag : int  }

let cnt = ref 0

let fresh content =
    let rec c = { father = c; rank = 1; desc = content; tag = !cnt  } in
    incr cnt; c

let rec find c =
  let f = c.father in
  if f == c then f
  else
    let f = find f in
    c.father <- f;
    f

let desc c = (find c).desc
let tag c = (find c).tag

let union f x y =
  let rx = find x and ry = find y in
  let ndesc = f rx.desc ry.desc in
  if rx != ry then 
    if rx.rank > ry.rank then begin
      ry.father <- rx;
      rx.desc <- ndesc
    end else if rx.rank < ry.rank then begin
      rx.father <-ry;
      ry.desc <- ndesc
    end else begin 
      ry.father <- rx;
      rx.rank <- rx.rank + 1;
      rx.desc <- ndesc
    end
  else ()


let equal x y = find x == find y
