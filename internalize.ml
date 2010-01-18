(* This module transforms a Parsetree.t into a Ast.ParseT.t;
   For this, we need to build unique variables for each variable (string) in the
   parse tree. The following simplifications take place:
     * type definitions are expanded
     * sequences e1; e2 are transformed to let _ = e1 in e2 
   *)

module I = Parsetree
module IT = ParseTypes
open Ast
open CommonInternalize

let rec ast' env = function
  | I.Const c -> Const c
  | I.Var (v,i) -> Var (var env v,([],[],List.map (effect env) i))
  | I.App (e1,e2,f,c) -> 
      App (ast env e1, ast env e2, f, List.map (rvar env) c)
  | I.Lam (x,t,cap,p,e,q) ->
      let env, nv = add_var env x in
      Lam (nv,ty env t, List.map (rvar env) cap,  pre env p, ast env e, post env q)
  | I.Let (g,e1,x,e2,r) ->
      let env, nv, g , e1, r = letgen env x g e1 r in
      let e2 = ast env e2 in
      Let (g, e1,Name.close_bind nv e2, r)
  | I.PureFun (x,t,e) ->
      let env, x = add_var env x in
      PureFun (ty env t, Name.close_bind x (ast env e))
  | I.Quant (k,x,t,e) ->
      let env, x = add_var env x in
      Quant (k,ty env t, Name.close_bind x (ast env e))
  | I.Ite (e1,e2,e3) -> Ite (ast env e1, ast env e2, ast env e3)
  | I.Annot (e,t) -> Annot (ast env e, ty env t)
  | I.Param (t,e) -> Param (ty env t, effect env e)
  | I.For (dir,p,i,st,en,e) ->
      let d = var env dir in
      let env,i = add_var env i in
      For (d, pre env p, i,var env st,var env en, ast env e)
  | I.LetReg (rl,e) -> 
      let env, nrl = add_rvars env rl in
      LetReg (nrl, ast env e)
  | I.Seq (e1,e2) -> 
      Let (G.empty, ParseT.annot (ast env e1) Ty.unit e1.I.loc, 
           Name.close_bind (Name.new_anon ()) (ast env e2), Const.NoRec)
and post env x = 
  let env, old = add_var env "old" in
  let env, cur = add_var env "cur" in
  let p = 
    match x with
      | I.PNone -> PNone
      | I.PPlain e -> PPlain (ast env e)
      | I.PResult (x,e) ->
          let env,nv = add_var env x in
          PResult (nv, ast env e) in
  old,cur,p
and pre env x = 
  let env, cur = add_var env "cur" in
  cur, Misc.opt_map (ast env) x

  
and ast env {I.v = v; loc = loc} : Ast.ParseT.t = 
  { Ast.v = ast' env v; loc = loc; t = (); e = NEffect.empty }

and letgen env x g e r = 
  let env', g = add_gen env g in
  let nv = Name.from_string x in
  let env' = 
    match r with 
    | Const.NoRec | Const.LogicDef -> env' 
    | Const.Rec _ -> add_ex_var env' x nv in
  let e = ast env' e in
  let env = add_ex_var env x nv in
  let r = rec_ env' r in
  env, nv, g, e, r

let rec decl env d = 
  match d with
  | I.Logic (n,g,t) -> 
      let env, g = add_gen env g in
      let env, nv = add_var env n in
      env, Logic (nv,g, ty env t)
  | I.Axiom (s,g,t) -> 
      let env', g = add_gen env g in
      env,Formula (s, ParseT.gen g (ast env' t), `Assumed)
  | I.Section (s,cl, dl) ->
      let env, dl = theory env dl in
      env, Section (s,cl,dl)
  | I.TypeDef (g,t,n) ->
      let env', g = add_gen env g in
      let t = Misc.opt_map (ty env') t in
      let env,nv = add_tvar env n g t in
      env, TypeDef (g, t, nv)
  | I.DLetReg rl -> 
      let env, nrl = add_rvars env rl in
      env, DLetReg nrl
  | I.Program (x,g,e,r) ->
      let env, nv, g , e, r = letgen env x g e r in
      env, Program (nv, g, e, r)
and theory x = Misc.list_fold_map decl x

let theory th = 
  let _, th = theory empty th in
  th
