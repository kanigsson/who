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
open CommonInternalize
module I = AnnotParseTree
module PI = Predefined.Identifier

let dummy = Name.new_anon ()

exception Error of string * Loc.loc

let error loc s =
  Myformat.ksprintf (fun s -> raise (Error (s,loc))) s

let inst env (tl,rl,el) =
  List.map (ty env) tl, List.map (Env.rvar env) rl, List.map (effect env) el

let add_var env x g =
  let env, x = Env.add_var env x in
  Env.only_add_type env x g, x

let add_ex_var env x g nv =
  let env = Env.add_ex_var env x nv in
  Env.only_add_type env nv g

let add_svar env x t = add_var env x (G.empty, t)

let typed_var logic env x =
  try
    let x = Env.var env x in
    let g,t = Env.lookup_type env x in
    let t = if logic then Ty.to_logic_type t else t in
    x, (g,t)
  with Not_found ->
    error Loc.dummy "undefined var: %s@." x

let rec term logic env (t : I.t) =
  let l = t.I.loc in
  match t.I.v with
  | I.Const c -> const c l
  | I.Var (x,i) ->
      let x, g = typed_var logic env x in
      var x (inst env i) g l
  | I.App (t1,t2,kind,cap) ->
      app ~kind ~cap:(List.map (Env.rvar env) cap)
        (term logic env t1) (term logic env t2) l
  | I.Lam (x,t,cap, p, e, q) ->
      let t = ty env t in
      let env, nv = add_svar env x t in
      caplam nv t (List.map (Env.rvar env) cap)
        (term true env p) (term false env e)
        (term true env q) l
  | I.HoareTriple (p,e,q) ->
      hoare_triple (term true env p) (term false env e) (term true env q) l
  | I.Let (g,e1,x,e2,r) ->
      let env, nv, g , e1, r = letgen env x g e1 r in
      let e2 = term logic env e2 in
      let_ g e1 nv e2 r l
  | I.PureFun (t,x,e) ->
      let t = ty env t in
      let env, x = add_svar env x t in
      plam x t (term logic env e) l
  | I.Quant (k,t,x,e) ->
      let t = ty env t in
      let env, x = add_svar env x t in
      squant k x t (term logic env e) l
  | I.LetReg (rl,e) ->
      let env, nrl = Env.add_rvars env rl in
      letreg nrl (term logic env e) l
  | I.Ite (e1, e2, e3) ->
      ite ~logic (term logic env e1) (term logic env e2) (term logic env e3) l
  | I.Annot (e,t) -> annot (term logic env e) (ty env t)
  | I.Gen (g,e) ->
      let env, g = Env.add_gen env g in
      gen g (term logic env e) l
(*
  | I.Tuple tl ->
      let tl = List.map (term logic env) tl in
      let n = List.length tl in
      let tyl = List.map (fun x -> x.t) tl in
      let mktup = R.predef (PI.mk_tuple_id n) (tyl,[],[]) l in
      R.appn mktup tl l
*)
  | I.Param (t,e) -> param (ty env t) (effect env e) l
and letgen env x g e r =
  let env', g = Env.add_gen env g in
  let nv = Name.from_string x in
  let env', logic =
    match r with
    | Const.NoRec -> env', false
    | Const.LogicDef -> env', true
    | Const.Rec t -> add_ex_var env' x (G.empty, ty env t) nv, false in
  let e = term logic env' e in
  let env = add_ex_var env x (g,e.Ast.t) nv in
  let r = rec_ env' r in
  env, nv, g, e, r

let rec decl env d =
  match d with
  | I.Logic (n,g,t) ->
      let env, g = Env.add_gen env g in
      let t = ty env t in
      let env, nv = add_var env n (g,t) in
      env, Logic (nv,g, t)
  | I.Axiom (s,t) ->
      env,Formula (s, term true env t, `Assumed)
  | I.Goal (s,t) ->
      env,Formula (s, term true env t, `Proved)
  | I.Section (s,cl, dl) ->
      let env, dl = theory env dl in
      env, Section (s,cl,dl)
  | I.TypeDef (g,t,n) ->
      let env', g = Env.add_gen env g in
      let t = Opt.map (ty env') t in
      let env,nv = Env.add_tvar env n g t in
      env, TypeDef (g, t, nv)
  | I.DLetReg rl ->
      let env, nrl = Env.add_rvars env rl in
      env, DLetReg nrl
  | I.Program (x,g,e,r) ->
      let env, nv, g , e, r = letgen env x g e r in
      env, Program (nv, g, e, r)
  | I.DGen g ->
      let env, g = Env.add_gen env g in
      env, DGen g
and theory env th = ExtList.fold_map decl env th


let theory th =
  let _, th = theory Env.empty th in
  th
