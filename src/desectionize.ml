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

module type T = sig
  type t
  val is_goal : t -> bool
  val is_section : t -> t list option
end
module Make (X : T) = struct

  let is_goal = X.is_goal
  let is_not_goal d = not (is_goal d)

  (* transform a theory ( = list of declarations) which may contain sections
   * into a list of theories without sections *)
  let rec desectionize acc cur th =
    (* this function scans a list of declarations;
     * [cur] - the list of declarations to which we add
             the currently scanned declaration ( if it is
             not a section)
       [acc] - the list of the theories established up to now *)
    match th with
    | [] ->
        (* we have established a new theory - add it to [acc] *)
        cur::acc
    | d::ds ->
        let acc, cur =
          match X.is_section d with
          | Some l ->
              (* take the current prefix [cur], without its lemmas
                 and use it to build all the theories in this
                 section; then, go on with the unchanged
                prefix *)
              desectionize acc (List.filter is_not_goal cur) l,cur
          | None ->
              (* if the scanned decl is not a [Section], add it to
               * the current theory and go on *)
              acc, d::cur in
        desectionize acc cur ds

  (* remove useless declarations at the end of a theory;
     i.e., all declarations not followed by at least one goal are useless *)
  let rec simplify l =
    (* assume that the theory comes in reverse order *)
    match l with
    | [] -> []
    | x::xs -> if is_goal x then l else simplify xs

  let theory th =
    (* l is a list of possible self-contained theories *)
    let l = desectionize [] [] th in
    (* remove useless hypothesis *)
    let l  = List.map simplify l in
    let l = List.filter (fun x -> x <> []) l in
    List.rev (List.map List.rev l)
end

module Input = struct
  open Ast
  type t = decl
  let is_goal d =
    match d with
    | Formula (_,_, `Proved) -> true
    | _ -> false

  let is_section d =
    match d with
    | Section (_,l,`Structure) -> Some l
    | _ -> None
end

module M = Make (Input)
include M
