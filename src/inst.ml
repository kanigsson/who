(************************************************************************************)
(*                                                                                  *)
(*                      Who                                                         *)
(*                                                                                  *)
(*       A simple VCGen for higher-order programs.                                  *)
(*                                                                                  *)
(*  Copyright (C) 2009, 2010, Johannes Kanig                                        *)
(*  Contact: kanig@lri.fr                                                           *)
(*                                                                                  *)
(*  Who is free software: you can redistribute it and/or modify it under the terms  *)
(*  of the GNU Lesser General Public License as published by the Free Software      *)
(*  Foundation, either version 3 of the License, or any later version.              *)
(*                                                                                  *)
(*  Who is distributed in the hope that it will be useful, but WITHOUT ANY          *)
(*  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR   *)
(*  A PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more       *)
(*  details.                                                                        *)
(*                                                                                  *)
(*  You should have received a copy of the GNU Lesser General Public License along  *)
(*  with this program.  If not, see <http://www.gnu.org/licenses/>                  *)
(************************************************************************************)

type ('a,'b,'c) t = 'a list * 'b list * 'c list 

let empty = [],[],[]
let is_empty x = x = empty

open Myformat
let prl pr = print_list comma pr
let prsl pr fmt l = 
  if l = [] then () else 
    fprintf fmt "@ %a" (print_list space pr) l

let print ?(kind=`Who) ~intype pra prb prc fmt ((tl,rl,el) as g) =
  if is_empty g then () else
    match kind with
    | `Who -> 
        (* separate types with comma, the others by spaces *)
        fprintf fmt "[%a|%a|%a]" (prl pra) tl (prsl prb) rl (prsl prc) el
    | `Coq -> 
        if intype then
          fprintf fmt "%a%a%a" (prsl pra) tl (prsl prb) rl (prsl prc) el
    | `Pangoline -> 
        if tl = [] then () else fprintf fmt "[%a]" (prl pra) tl


let map fa fb fc (tl,rl,el) =
  List.map fa tl, List.map fb rl, List.map fc el

let iter2 fa fb fc (tl1,rl1,el1) (tl2,rl2,el2) =
  List.iter2 fa tl1 tl2;
  List.iter2 fb rl1 rl2;
  List.iter2 fc el1 el2

let equal eqa eqb eqc (tl1,rl1,el1) (tl2,rl2,el2) =
  try 
    List.for_all2 eqa tl1 tl2 &&
    List.for_all2 eqb rl1 rl2 &&
    List.for_all2 eqc el1 el2
  with Invalid_argument _ -> false
