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

open Ty
open Ast
open Recon

let id x = x
let rec normalize_term v = normalize v id
and normalize e k =
  let loc = e.loc in
  match e.v with
  | (Const _ | Ast.Var _ | Param _ ) -> k e
  | Lam (x,t,(p,e,q)) ->
(*       Format.printf "found effectful function %a@." Name.print x; *)
      k (lam x t (normalize_term p)
        (normalize_term e) (normalize_term q) loc)
  | PureFun (t,b)->
      let x,e = vopen b in
      k (plam x t (normalize_term e) loc)
  | Let (g,e1,b) ->
      let x,e2 = vopen b in
      normalize e1 (fun v -> let_ g v x (normalize e2 k) Const.NoRec loc)
  | LetRec (g,t,b) ->
      let x,e1,e2 = recopen b in
      normalize e1 (fun v -> let_ g v x (normalize e2 k) (Const.Rec t) loc)
  | LetReg (l,e) -> k (letreg l (normalize_term e) loc)
  | Gen (g,e) -> k (gen g (normalize_term e) loc)
  | Quant (kind,t,b) ->
      let x, e = vopen b in k (squant kind x t (normalize_term e) loc)
  | Case (e1,bl) ->
      normalize_name e1 (fun v -> k (case v (List.map branch bl) loc))
  | Ite (e1,e2,e3) ->
      normalize_name e1
        (fun v ->
          k (ite ~logic:false v (normalize_term e2) (normalize_term e3) loc))
  | App (e1,e2) ->
(*       Format.printf "applying: %a@." print e1; *)
      normalize_name e1
        (fun v1 -> normalize_name e2
          (fun v2 -> k (app v1 v2 loc)))
  | HoareTriple (p,e,q) ->
(*       Format.printf "found hoare_triple@."; *)
      k (hoare_triple (normalize_term p)
        (normalize_term e) (normalize_term q) loc)
  | SubEff (e,eff) -> k (subeff (normalize_term e) eff loc)
and branch b =
  let nvl,p,e = popen b in
  let e = normalize_term e in
  pclose nvl p e

and normalize_name e k =
  normalize e
    (fun e ->
      if is_value e then k e
      else
        let nv = Name.from_string "anf" in
        let nvv = svar (mk_var_with_type false `Prefix nv e.t) e.loc in
        let_ Generalize.empty e nv (k nvv) Const.NoRec e.loc)

let term = normalize_term

let rec decl d =
  match d with
  | Logic _ | TypeDef _ | DLetReg _ | DGen _
  | Decl _ | Inductive _  -> d
  | Formula (s,t,r) -> Formula (s, term t, r)
  | Section (s,th, kind) -> Section (s, theory th, kind)
  | Program (n,g,t,r) -> Program (n,g,term t, r)

and theory th = List.map decl th
