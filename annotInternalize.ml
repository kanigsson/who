open Ast
open CommonInternalize
module I = AnnotParseTree

let dummy = Name.new_anon ()
module R = Recon

let inst env (tl,rl,el) = 
  List.map (ty env) tl, List.map (rvar env) rl, List.map (effect env) el

let only_add_type env x g = 
  { env with typing = NM.add x g env.typing }
let add_var env x g = 
  let env, x = add_var env x in
  { env with typing = NM.add x g env.typing }, x

let add_svar env x t = add_var env x (G.empty, t)

let typed_var env x = 
  let x = var env x in
  let g = NM.find x env.typing in
  x, g

let rec term env (t : I.t) = 
  let l = t.I.loc in
  match t.I.v with
  | I.Const c -> R.const c l
  | I.Var (x,i) -> 
      let x, g = typed_var env x in
      R.var x (inst env i) g l
  | I.App (t1,t2,kind,cap) -> 
      R.app ~kind ~cap:(List.map (rvar env) cap) (term env t1) (term env t2) l
  | I.Lam (x,t,cap, p, e, q) -> 
      let t = ty env t in
      let env, nv = add_svar env x t in
      R.caplam nv t (List.map (rvar env) cap) 
        (dummy, Some (term env p)) (term env e) 
        (dummy, dummy, PPlain (term env q)) l
  | I.Let (g,e1,x,e2,r) -> 
      let env, nv, g , e1, r = letgen env x g e1 r in
      let e2 = term env e2 in
      R.let_ g e1 nv e2 r l
  | I.PureFun (t,x,e) ->
      let t = ty env t in
      let env, x = add_svar env x t in
      R.plam x t (term env e) l
  | I.Quant (k,t,x,e) ->
      let t = ty env t in
      let env, x = add_svar env x t in
      R.squant k x t (term env e) l
  | I.LetReg (rl,e) -> 
      let env, nrl = add_rvars env rl in
      R.letreg nrl (term env e) l
  | I.Ite (e1, e2, e3) -> 
      R.ite (term env e1) (term env e2) (term env e3) l
  | I.Annot (e,t) -> R.annot (term env e) (ty env t)
  | I.Gen (g,e) -> 
      let env, g = add_gen env g in
      R.gen g (term env e) l
  | I.Param (t,e) -> R.param (ty env t) (effect env e) l
and letgen env x g e r = 
  let env', g = add_gen env g in
  let nv = Name.from_string x in
  let env' = 
    match r with 
    | Const.NoRec | Const.LogicDef -> env' 
    | Const.Rec _ -> add_ex_var env' x nv in
  let e = term env' e in
  let env = add_ex_var env x nv in
  let env = only_add_type env nv (g,e.Ast.t) in
  let r = rec_ env' r in
  env, nv, g, e, r

let rec decl env d = 
  match d with
  | I.Logic (n,g,t) -> 
      let env, g = add_gen env g in
      let t = ty env t in
      let env, nv = add_var env n (g,t) in
      env, Logic (nv,g, t)
  | I.Axiom (s,t) -> 
      env,Formula (s, term env t, `Assumed)
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
and theory env th = Misc.list_fold_map decl env th


let theory th = 
  let _, th = theory empty th in
  th
