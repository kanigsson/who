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

open Ast
module PL = Predefined.Logic
module PI = Predefined.Identifier
module N = Name
module M = N.M

type t = N.t M.t * N.t M.t

let e_combine (r1,e1) (r2,e2) = 
  M.fold M.add r2 r1,
  M.fold M.add e2 e1

let e_restrict d (r,e) = 
  M.fold (fun k v acc -> 
    if Effect.rmem d k then M.add k v acc else acc) r M.empty,
  M.fold (fun k v acc -> 
    if Effect.emem d k then M.add k v acc else acc) e M.empty

let get_reg x (rm,_) = M.find x rm

let rec from_form d x = 
(*   Myformat.printf "finding effrec for %a@." print' x; *)
  match destruct_app2_var x with
  | Some (v,_, m1,m2) when PL.equal v PI.combine_id ->
      e_combine (from_form_t m1.t m1) (from_form_t m2.t m2)
  | None | Some _ -> 
      match destruct_app x with
      | Some ({v = Var (v,([],[],[_;e2]))}, m) when PL.equal v PI.restrict_id ->
          e_restrict e2 (from_form_t m.t m)
      | None | Some _ ->
          match x.v with
          | Var (s,_) -> 
              Effect.rfold (fun k acc -> M.add k s acc) M.empty d,
              Effect.efold (fun k acc -> M.add k s acc) M.empty d 
          | _ -> 
              Myformat.printf "strange term: %a@." print x;
              assert false
and from_form_t t x = from_form (Ty.domain t) x

let rfold f (r,_) acc = M.fold f r acc
let efold f (_,e) acc = M.fold f e acc
