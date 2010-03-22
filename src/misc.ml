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

open Format

let lineno = ref 0
let newlinepos = ref 0

let pair_compare cmpa cmpb (a1,b1) (a2,b2) =
  let c = cmpa a1 a2 in
  if c = 0 then cmpb b1 b2 else c

let pair_equal eqa eqb (a1,b1) (a2,b2) = eqa a1 a2 && eqb b1 b2

let cnt =
  let x = ref 0 in
    fun () -> incr x ; !x

let rec list_compare cmp l1 l2 = 
  match l1,l2 with
  | [],[] -> 0
  | [],_ -> 1
  | _,[] -> -1
  | (h1::r1), (h2::r2) -> 
      let c = cmp h1 h2 in
      if c <> 0 then c
      else list_compare cmp r1 r2

let list_equal cmp l1 l2 = list_compare cmp l1 l2 = 0
let opt_equal eq o1 o2 = 
  match o1, o2 with
  | None, None -> true
  | Some t1, Some t2 -> eq t1 t2
  | _, _ -> false

let list_mem eq x l = List.exists (fun b -> eq x b) l
let list_contained eq l1 l2 = 
  List.for_all (fun a -> list_mem eq a l2) l1

let list_equal_unsorted eq l1 l2 = 
  list_contained eq l1 l2 && list_contained eq l2 l1

let list_union eq l1 l2 = 
  List.fold_left
    (fun acc x -> if list_mem eq x acc then acc else x :: acc) l2 l1

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module SS = StringSet

let rec fold_down f acc n = 
  if n <= 0 then acc
  else fold_down f (f acc n) (n-1)

let id x = x

let map_filter map filter l = 
  let rec aux = function
  | [] -> []
  | x::xs ->
      let x = map x in
      let xs = aux xs in
      if filter x then x :: xs else xs
  in
  aux l

let fold_left_rev_map f acc l = 
  List.fold_left
    (fun (acc,l) d ->
      let acc, d = f acc d in
      acc, d::l
    ) (acc,[]) l

let fold_map f acc l = 
  let rec aux acc = function
    | [] -> []
    | x::xs ->
        let acc, x = f acc x in
        x :: aux acc xs
  in
  aux acc l
        
let list_fold_map f init l =
  let rec flm acu l' = function
    | [] ->
        (acu, List.rev l')
    | x :: xs ->
        let (acu, y) = f acu x in
          flm acu (y :: l') xs
  in
    flm init [] l

let repeat ?(from=0) n f = 
  let rec loop i accu = 
    if i = n then List.rev accu 
    else loop (i + 1) (f i :: accu)
  in
    loop from []

let opt_map f = function
  | None -> None
  | Some x -> Some (f x)

let find_first p iter t def =
  let x = ref def in
  begin try 
    iter (fun z -> 
      if p z then begin x := z; raise Exit end else ()) t
  with Exit -> () end;
  !x
