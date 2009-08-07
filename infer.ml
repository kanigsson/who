open Unify
open Clean_ast
module SM = Misc.StringMap

type env = { n : int ; vars : (int * ty) SM.t }

exception Error of string

let error s = raise (Error s)

let add_var env x t = { env with vars = SM.add x (env.n,t) env.vars }

let type_of_constant = function
  | Const.Int _ -> Const.Int
  | Const.Void -> Const.Unit
  | Const.Btrue | Const.Bfalse -> Const.Bool

let rec infer' env t = function
  | App (e1,e2) ->
      let nt = new_ty env.n in
      infer env (arrow nt t) e1;
      infer env nt e2
  | Var x ->
      begin try
        let m,xt = VM.find x env.vars in
        let t' = refresh_ty ~old:m ~new_:env.n xt in
        unify xt t'
      with Not_found -> 
        error (Misc.mysprintf "variable %a not found" Var.print x)
      end
  | Const c ->
      unify t (const (type_of_constant c))
  | Lam (x,e) ->
      let nt = new_ty env.n in
      let nt2 = new_ty env.n in
      let () = unify (arrow nt nt2) t in
      let env = add_var env x nt in
      infer env nt2 e
  | Let (e1,x,e2) ->
      let nt = new_ty env.n in
      infer {env with n = env.n + 1 } nt e1;
      let env = add_var env x nt in
      infer env t e2
and infer env t e = 
  { v = infer' env t e.v; t = t }

let infer e = 
  let nt = new_ty 0 in
  infer { vars = Initial.infer_env; n = 0 } nt e


open Format

let rec print_node fmt (U x) = 
  let x = Uf.find x in
  match Uf.desc x with
  | Var n -> fprintf fmt "%d" n
  | Arrow (t1,t2) -> fprintf fmt "(%a -> %a)" print_node t1 print_node t2
  | Const c -> Ty.print_const fmt c


let print_ast fmt x = 
  print (fun fmt x -> fprintf fmt " : %a]" print_node x) 
    DontCare.open_bind fmt x
