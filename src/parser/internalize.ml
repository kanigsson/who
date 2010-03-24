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

(* This module transforms a ParseTree.t into a Ast.ParseT.t;
   For this, we need to build unique variables for each variable (string) in the
   parse tree. The following simplifications take place:
     * type definitions are expanded
     * sequences e1; e2 are transformed to let _ = e1 in e2
   *)

type env = CommonInternalize.Env.t
module I = ParseTree
module IT = ParseTypes
open CommonInternalize
open InternalParseTree

let rec ast' env = function
  | I.Const c -> Const c
  | I.Var (v,i) ->
      Var (Env.var env v,List.map (effect env) i)
  | I.App (e1,e2,f,c) ->
      App (ast env e1, ast env e2, f, List.map (Env.rvar env) c)
  | I.Lam (x,t,cap,p,e,q) ->
      let env, nv = Env.add_var env x in
      Lam (nv, ty env t, List.map (Env.rvar env) cap,
            (pre env p, ast env e, post env q))
  | I.Let (g,e1,x,e2,r) ->
      let env, nv, g , e1, r = letgen env x g e1 r in
      let e2 = ast env e2 in
      Let (g, e1,Name.close_bind nv e2, r)
  | I.PureFun (x,t,e) ->
      let env, x = Env.add_var env x in
      PureFun (MutableType.from_ty (ty env t),
               Name.close_bind x (ast env e))
  | I.Quant (k,x,t,e) ->
      let env, x = Env.add_var env x in
      Quant (k, MutableType.from_ty (ty env t),
             Name.close_bind x (ast env e))
  | I.Ite (e1,e2,e3) -> Ite (ast env e1, ast env e2, ast env e3)
  | I.Annot (e,t) -> Annot (ast env e, ty env t)
  | I.Param (t,e) -> Param (ty env t, effect env e)
  | I.For (dir,p,i,st,en,e) ->
      let d = Env.var env dir in
      let env,i = Env.add_var env i in
      For (d, pre env p, i,Env.var env st, Env.var env en, ast env e)
  | I.LetReg (rl,e) ->
      let env, nrl = Env.add_rvars env rl in
      LetReg (nrl, ast env e)
  | I.Seq (e1,e2) ->
      Let (G.empty, annot (ast env e1) Ty.unit e1.I.loc,
           Name.close_bind (Name.new_anon ()) (ast env e2), Const.NoRec)
  | I.Restrict (t,e) ->
      let t = ast env t and e = effect env e in
      Restrict (t,e)
  | I.HoareTriple (p,e,q) ->
      let p = pre env p and q = post env q and e = ast env e in
      HoareTriple (p,e,q)

and post env x =
  let env, old = Env.add_var env "old" in
  let env, cur = Env.add_var env "cur" in
  let p =
    match x with
      | I.PNone -> PNone
      | I.PPlain e -> PPlain (ast env e)
      | I.PResult (x,e) ->
          let env,nv = Env.add_var env x in
          PResult (nv, ast env e) in
  old,cur,p
and pre env x =
  let env, cur = Env.add_var env "cur" in
  cur, Misc.opt_map (ast env) x


and ast env {I.v = v; loc = loc} = { v = ast' env v; loc = loc }

and letgen env x g e r =
  let env', g = Env.add_gen env g in
  let nv = Name.from_string x in
  let env' =
    match r with
    | Const.NoRec | Const.LogicDef -> env'
    | Const.Rec _ -> Env.add_ex_var env' x nv in
  let e = ast env' e in
  let env = Env.add_ex_var env x nv in
  let r = rec_ env' r in
  env, nv, g, e, r

let rec decl env d =
  match d with
  | I.Logic (n,g,t) ->
      let env, g = Env.add_gen env g in
      let env, nv = Env.add_var env n in
      env, Logic (nv,g, ty env t)
  | I.Axiom (s,g,t) ->
      let env', g = Env.add_gen env g in
      let t = ast env' t in
      env,Formula (s, gen g t t.loc, `Assumed)
  | I.Section (s,cl, dl) ->
      let env, dl = theory env dl in
      env, Section (s,cl,dl)
  | I.TypeDef (g,t,n) ->
      let env', g = Env.add_gen env g in
      let t = Misc.opt_map (ty env') t in
      let env,nv = Env.add_tvar env n g t in
      env, TypeDef (g, t, nv)
  | I.DLetReg rl ->
      let env, nrl = Env.add_rvars env rl in
      env, DLetReg nrl
  | I.Program (x,g,e,r) ->
      let env, nv, g , e, r = letgen env x g e r in
      env, Program (nv, g, e, r)
and theory x = Misc.list_fold_map decl x

let prelude_env, prelude =
  theory Env.empty
    (Parser.main Lexer.token (Lexing.from_string Prelude.prelude))

let theory th =
  let _, th = theory prelude_env th in
  th
