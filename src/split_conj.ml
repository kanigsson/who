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

let split_formula : t -> t list =
  let rec aux f =
    let l = f.loc in
    match f.v with
    | Quant (`FA,t,b) ->
        let x,f = vopen b in
        List.map (fun f -> squant `FA x t f l) (aux f)
    | Gen (g,f) ->
        List.map (fun f -> gen g f l) (aux f)
    | _ ->
        begin match destruct_app2_var f with
        | Some (v, _, f1, f2) when id_equal v I.and_id ->
            aux f1 @ aux f2
        | Some (v, _, h, g) when id_equal v I.impl_id ->
            List.map (fun f -> impl h f l) (aux g)
        | _ -> [f]
        end
  in
  aux

let declfun d =
  match d with
  | Formula (n,f,`Proved) ->
      let l = split_formula f in
      List.fold_right
        (fun x acc ->
          match mk_goal (Name.new_name n) x with
          | None -> acc
          | Some d -> d ::acc) l []
 | _ -> [d]

let theory t = theory_map ~declfun t

