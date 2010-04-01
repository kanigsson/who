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

open Name
open Ast

module PL = Predefined
module G = Ty.Generalize

let intro_eq f = function
  | Formula (_,x,`Assumed) -> equal x f
  | _ -> false

let to_section th =
  let rec decl_to_outdecl d =
    match d with
    | DLetReg _ | Program _ -> assert false
    | DGen _ | Decl _ | TypeDef _ | Formula (_,_,`Assumed) | Logic _ -> [ d ]
    | Formula (s,f, `Proved) -> mk_Section ~namehint:s f
    | Section (n,th, k) ->
        let l = List.flatten (List.map decl_to_outdecl th) in
        [Section (n,l,k)]
  and term_intro (f : Ast.t) : decl list * Ast.t =
    (* take a formula and cut it into two parts : intro and the rest *)
    let rec aux acc f =
      match f.v with
      | Quant (`FA, t,b) ->
          let x , f = vopen b in
          aux (Logic (x,(Ty.Generalize.empty,t)) :: acc) f
      | Ast.Gen (g,f) ->
          if Ty.Generalize.is_empty g then aux acc f
          else aux ((DGen g)::acc) f
      | f' ->
          match destruct_app2_var' f' with
          | Some (v,_,f1,f2) when PL.equal v I.impl_id  ->
              aux (Formula (Name.from_string "H", f1,`Assumed)::acc) f2
          | _ -> List.rev acc, f in
    aux [] f
  and make_PO ?namehint ( f : Ast.t) : decl list =
    let rec aux acc f =
      match f.v with
      | Quant (`FA,_,_) | Ast.Gen _ ->
          mk_Section f @ acc
      | f' ->
          match destruct_app2_var' f' with
          | Some (v,_,_,_) when PL.equal v I.impl_id -> mk_Section f @ acc
          | Some (v,_,f1,f2) when PL.equal v I.and_id -> aux (aux acc f2) f1
          | _ ->
              let n =
                match namehint with
                | None -> Name.from_string "goal"
                | Some n -> n in
              Formula (n, f,`Proved) :: acc
    in
    aux [] f
  and mk_Section ?namehint (f : Ast.t) : decl list =
    let il, f' = term_intro f in
    match make_PO ?namehint f' with
    | [] -> []
    | [x] when List.length il = 0 -> [x]
    | l -> [Section (Name.from_string "sec", il@l,`Structure)]
  in
  List.flatten (List.map decl_to_outdecl th)
