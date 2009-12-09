(* This module transforms a Parsetree.t into a Ast.ParseT.t;
   For this, we need to build unique variables for each variable (string) in the
   parse tree. The following simplifications take place:
     * type definitions are expanded
     * sequences e1; e2 are transformed to let _ = e1 in e2 
  Also, we enter global names (types and variables) into a table stored in the
  [Ty] module. We need to do this to save the chosen names for the predefined
  variables, such as +, /\, ...
   *)

module I = Parsetree
open Ast


module SM = Misc.StringMap
module G = Ty.Generalize
module NM = Name.M

(* the environment maps each variable name to a 
   unique name *)
type env = 
  { 
    v : Name.t SM.t ;
    t : Name.t SM.t ;
    r : Name.t SM.t ;
    e : Name.t SM.t ;
    tyrepl : (Ty.Generalize.t * Ty.t) NM.t
  }

exception UnknownVar of string
let error s = raise (UnknownVar s)
let gen_var s m x = try SM.find x m with Not_found -> error (s ^ " var: " ^ x)

let var env = gen_var "program" env.v
let tyvar env = gen_var "type" env.t
let rvar env = gen_var "region" env.r
let effvar env = gen_var "effect" env.e

let add_var env x = 
  let y = Name.from_string x in
  { env with v = SM.add x y env.v }, y

let add_ex_var env x y = 
  { env with v = SM.add x y env.v }

let add_tvar env x g t = 
  let y = Name.from_string x in
  { env with t = SM.add x y env.t;
    tyrepl = 
       match t with
       | None -> env.tyrepl
       | Some t -> NM.add y (g,t) env.tyrepl
  }, y

let add_rvars env l = 
  let r, nl = 
    List.fold_left
      (fun (r,l) x ->
        let nv = Name.from_string x in
        SM.add x nv r, nv::l) (env.r,[]) l in
  { env with r = r }, nl

let add_tvars env l = 
  List.fold_left (fun (acc,l) x -> 
    let env, nv = add_tvar acc x Ty.Generalize.empty None in
    env, nv::l) (env,[]) l

let add_evars env l = 
  let e, nl = 
    List.fold_left
      (fun (e,l) x ->
        let nv = Name.from_string x in
        SM.add x nv e, nv::l) (env.e,[]) l in
  { env with e = e }, nl

let add_gen env (tl,rl,el) =
  let env, tl = add_tvars env tl in
  let env, rl = add_rvars env rl in
  let env, el = add_evars env el in
  env, (List.rev tl,List.rev rl,List.rev el)

let effect env (rl,el) = 
  NEffect.from_lists
    (List.map (rvar env) rl)
    (List.map (effvar env) el)

let ty env t = 
  let rec aux = function
    | I.TVar v -> Ty.var (tyvar env v)
    | I.TConst c -> Ty.const c
    | I.Tuple (t1,t2) -> Ty.tuple (aux t1) (aux t2)
    | I.Arrow (t1,t2,e,cap) -> 
        Ty.caparrow (aux t1) (aux t2) (effect env e) (List.map (rvar env) cap)
    | I.PureArr (t1,t2) -> Ty.parr (aux t1) (aux t2)
    | I.TApp (v,i) -> 
        let v = tyvar env v in
        let i = inst i in
        begin try 
          let g,t = NM.find v env.tyrepl in
          Ty.allsubst g i t
        with Not_found -> Ty.app v i end
    | I.Ref (r,t) -> Ty.ref_ (rvar env r) (aux t)
    | I.Map e -> Ty.map (effect env e)
    | I.ToLogic t -> Ty.to_logic_type (aux t)
  and inst i = Inst.map aux (rvar env) (effect env) i in
  aux t

open Myformat

let print v env = 
  printf "%s : %a@." v (print_string_map Name.print) env.e

let rec ast' env = function
  | I.Const c -> Const c
  | I.Var v -> Var (var env v,([],[],[]))
  | I.App (e1,e2,f,c) -> 
      App (ast env e1, ast env e2, f, List.map (rvar env) c)
  | I.Lam (x,t,cap,p,e,q) ->
      let env, nv = add_var env x in
      Lam (nv,ty env t, List.map (rvar env) cap,  pre env p, ast env e, post env q)
  | I.Let (p,g,e1,x,e2,r) ->
      let env', g' = add_gen env g in
      let nv = Name.from_string x in
      let env' = 
        match r with 
        | I.NoRec -> env' 
        | I.Rec _ -> add_ex_var env' x nv in
      let e1 = 
        match e1.I.v with 
        | I.Logic t ->
            let t = ty env' t in
            (* in the case of a logic, we save the chosen variable name *)
            Ty.add_var x (nv,g',t);
            { Ast.v = Logic t; loc = e1.I.loc; t = (); e = () }
        | _ -> ast env' e1 in
      let env = add_ex_var env x nv in
      let e2 = ast env e2 in
      Let (p,g', e1,Name.close_bind nv e2,rec_ env' r)
  | I.PureFun (x,t,e) ->
      let env, x = add_var env x in
      PureFun (ty env t, Name.close_bind x (ast env e))
  | I.Quant (k,x,t,e) ->
      let env, x = add_var env x in
      Quant (k,ty env t, Name.close_bind x (ast env e))
  | I.Ite (e1,e2,e3) -> Ite (ast env e1, ast env e2, ast env e3)
  | I.Axiom e -> Axiom (ast env e)
  | I.Logic t -> Logic (ty env t)
  | I.Annot (e,t) -> Annot (ast env e, ty env t)
  | I.TypeDef (g,t,x,e) ->
      let env', g = add_gen env g in
      let t = Misc.opt_map (ty env') t in
      let env,nv = add_tvar env x g t in
      (* we also save the type names *)
      Ty.add_tyvar x (nv,g);
      TypeDef (g, t, nv, ast env e)
  | I.Param (t,e) -> Param (ty env t, effect env e)
  | I.For (dir,p,i,st,en,e) ->
      let d = var env dir in
      let env,i = add_var env i in
      For (d, pre env p, i,var env st,var env en, ast env e)
  | I.LetReg (rl,e) -> 
      let env, nrl = add_rvars env rl in
      LetReg (nrl, ast env e)
  | I.Seq (e1,e2) -> 
      Let (false,G.empty, ParseT.annot (ast env e1) Ty.unit e1.I.loc, 
           Name.close_bind (Name.new_anon ()) (ast env e2), NoRec)
  | I.Section (n,f,e) -> 
      Section (n,f,ast env e)
  | I.EndSec e -> EndSec (ast env e)
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
    tyrepl = NM.empty;
  }
let main t = ast empty t
