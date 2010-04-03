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

let term env t =
  rebuild_map
    ~varfun:(fun z i def ->
      try
        let g,t = Name.M.find z env in
        allsubst g i t
      with Not_found -> def)
    ~termfun:(fun t ->
      match t.v with
      | Let (g,e1,b,_) ->
          let x,e2 = vopen b in
          polsubst g x e1 e2
      | Const _ | Var _ | App _ | Gen _ | PureFun _ | Quant _ | Ite _
      | Lam _ | LetReg _ | Param _ | HoareTriple _ -> t)
    t

let rec decl env d =
  match d with
  | Logic _ | TypeDef _ | DLetReg _ | DGen _ | Decl _  -> env, [d]
  | Formula (n,f,k) -> env, [Formula (n, term env f, k) ]
  | Inductive (n,g,t,tel) ->
      env, [Inductive (n,g,t, List.map (term env) tel)]
  | Section (s,th, kind) ->
      let env, th = theory env th in
      env, [Section (s,th, kind)]
  | Program (n,g,t,Const.LogicDef) -> Name.M.add n (g,term env t) env, []
  | Program _ -> assert false
and theory env th =
  let env, l = ExtList.fold_map decl env th in
  env, List.flatten l

let theory th =
  let _, th = theory Name.M.empty th in
  th

