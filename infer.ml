module A = Clean_ast
open Unify
module SM = Misc.StringMap

type env = { n : int ; vars : (int * ty) SM.t }

exception Error of string

let error s = raise (Error s)

let add_var env x t = 
  { env with vars = SM.add x (env.n,t) env.vars }

let type_of_constant = function
  | Const.Int _ -> Const.TInt
  | Const.Void -> Const.TUnit
  | Const.Btrue | Const.Bfalse -> Const.TBool

let rec infer' env t = function
  | A.App (e1,e2) ->
      let nt = new_ty env.n in
      infer env (arrow nt t) e1;
      infer env nt e2
  | A.Var x ->
      begin try
        let m,xt = SM.find x env.vars in
        unify (refresh_ty ~old:m ~new_:env.n xt) t
      with Not_found -> error (Misc.mysprintf "variable %s not found" x) end
  | A.Const c -> unify t (const (type_of_constant c))
  | A.Lam (x,e) ->
      let nt = new_ty env.n in
      let nt2 = new_ty env.n in
      unify (arrow nt nt2) t;
      let env = add_var env x nt in
      infer env nt2 e
  | A.Let (e1,x,e2) ->
      let nt = new_ty env.n in
      infer {env with n = env.n + 1 } nt e1;
      infer (add_var env x nt) t e2
and infer env t e = 
  e.A.t <- t; 
  infer' env t e.A.v

let infer e = 
  let nt = new_ty 0 in
  infer { vars = Initial.infer_env; n = 0 } nt e
