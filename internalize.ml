module I = Parsetree
open Vars
open Ast

module SM = Misc.StringMap

type env = 
  { 
    v : Var.t SM.t ;
    t : TyVar.t SM.t ;
    r : RVar.t SM.t ;
    e : EffVar.t SM.t ;
    global : bool;
  }

exception UnknownVar of string
let error s = raise (UnknownVar s)
let var env x = 
  try SM.find x env.v with Not_found -> error ("program var: " ^ x)
let tyvar env x = 
  try SM.find x env.t with Not_found -> error ("type var : " ^ x)
let rvar env x =
  try SM.find x env.r with Not_found -> error ("region var: " ^ x)
let effvar env x =
  try SM.find x env.e with Not_found -> error ("effect var: " ^ x)

let add_var env x = 
  let y = Var.from_string x in
  if env.global then Vars.add_var x y; 
  { env with v = SM.add x y env.v }, y

let add_ex_var env x y = 
  { env with v = SM.add x y env.v }

let add_tvar env x = 
  let y = TyVar.from_string x in
  { env with t = SM.add x y env.t }, y

let add_rvars env l = 
  let r, nl = 
    List.fold_left
      (fun (r,l) x ->
        let nv = RVar.from_string x in
        SM.add x nv r, nv::l) (env.r,[]) l in
  { env with r = r }, nl

let add_tvars env l = 
  List.fold_left (fun (acc,l) x -> 
    let env, nv = add_tvar acc x in
    env, nv::l) (env,[]) l

let add_evars env l = 
  let e, nl = 
    List.fold_left
      (fun (e,l) x ->
        let nv = EffVar.from_string x in
        SM.add x nv e, nv::l) (env.e,[]) l in
  { env with e = e }, nl

let add_gen env (tl,rl,el) =
  let env, tl = add_tvars env tl in
  let env, rl = add_rvars env rl in
  let env, el = add_evars env el in
  env, (tl,rl,el)

let rlist_to_set env l = 
  List.fold_left (fun acc x -> RVar.S.add (rvar env x) acc) RVar.S.empty l

let elist_to_set env l = 
  List.fold_left 
    (fun acc x -> 
      EffVar.S.add (effvar env x) acc) EffVar.S.empty l

let effect env (rl,el,cl) = 
  rlist_to_set env rl, elist_to_set env el, rlist_to_set env cl

let ty env t = 
  let rec aux = function
    | I.TVar v -> Ty.var (tyvar env v)
    | I.TConst c -> Ty.const c
    | I.Tuple (t1,t2) -> Ty.tuple (aux t1) (aux t2)
    | I.Arrow (t1,t2,e) -> Ty.arrow (aux t1) (aux t2) (effect env e)
    | I.PureArr (t1,t2) -> Ty.parr (aux t1) (aux t2)
    | I.TApp (v,i) -> Ty.app (tyvar env v) (inst i)
    | I.Ref (r,t) -> Ty.ref_ (rvar env r) (aux t)
    | I.Map e -> Ty.map (effect env e)
  and inst i = Inst.map aux (rvar env) (effect env) i in
  aux t

open Myformat
let print v env = 
  printf "%s : %a@." v (print_string_map EffVar.print) env.e
let rec ast' env = function
  | I.Const c -> Const c
  | I.Var v -> Var (var env v,([],[],[]))
  | I.App (e1,e2,f,c) -> App (ast env e1, ast env e2, f, List.map (rvar env) c)
  | I.Lam (x,t,p,e,q) ->
      let env, nv = add_var env x in
      Lam (nv,ty env t, pre env p, ast env e, post env q)
  | I.Let ((tl,rl,el) as g,e1,x,e2,r) ->
      let env', g' = add_gen env g in
(*
      printf "%s : %a@." x (print_list space pp_print_string) el;
      print x env';
*)
      let nv = Var.from_string x in
      if env.global then Vars.add_var x nv;
      let env' = 
        match r with 
        | I.NoRec -> env' 
        | I.Rec _ -> add_ex_var env' x nv in
      let e1 = ast {env' with global = false} e1 in
      let env = add_ex_var env x nv in
      let e2 = ast env e2 in
      Let (g',e1,nv,e2,rec_ env' r)
  | I.PureFun (x,t,e) ->
      let env, x = add_var env x in
      PureFun (x,ty env t, ast env e)
  | I.Quant (k,x,t,e) ->
      let env, x = add_var env x in
      Quant (k,x,ty env t, ast env e)
  | I.Ite (e1,e2,e3) -> Ite (ast env e1, ast env e2, ast env e3)
  | I.Axiom e -> Axiom (ast env e)
  | I.Logic t -> Logic (ty env t)
  | I.Annot (e,t) -> Annot (ast env e, ty env t)
  | I.TypeDef (g,t,x,e) ->
      let env', g = add_gen env g in
      let t = Misc.opt_map (ty env') t in
      let env,x = add_tvar env x in
      TypeDef (g, t, x, ast env e)
  | I.Param (t,e) -> Param (ty env t, effect env e)
  | I.For (dir,p,i,st,en,e) ->
      let d = var env dir in
      let env,i = add_var env i in
      For (d, pre env p, i,var env st,var env en, ast env e)
  | I.LetReg (rl,e) -> 
      let env, nrl = add_rvars env rl in
      LetReg (nrl, ast env e)
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

  
and rec_ env = function
  | I.Rec t -> Rec (ty env t)
  | I.NoRec -> NoRec
and ast env {I.v = v; loc = loc} = 
  { Ast.v = ast' env v; loc = loc; t = (); e = () }

let empty = 
  { v = SM.empty; t = SM.empty; 
    r = SM.empty; e = SM.empty;
    global = true;
  }
let main t = ast empty t
