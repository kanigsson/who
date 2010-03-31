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

let termfun t =
  let l = t.loc in
  match t.v with
  | Quant (k,Ty.Tuple tl, b) ->
    let x,f = vopen b in
    let vl, vtl = ExtList.split_map (fun t ->
      let v = Name.from_string "z" in
      (v,t), svar v t l) tl in
    let tuple = mk_tuple vtl l in
    let f = subst x (fun _ -> tuple) f in
    List.fold_right (fun (v,t) acc -> squant k v t acc l) vl f
  | _ -> t

let theory th = theory_map ~termfun th
