open Vars
open Ty2

module VM = Var.FreeMap
module Uf = Unionfind

type ty = U of ty Ty2.t' Uf.t
type env = { n : int ; vars : (int * ty) VM.t }

exception Error of string

let error s = raise (Error s)

let type_of_constant = function
  | Ast.Int _ -> Ty.Int
  | Ast.Void -> Ty.Unit
  | Ast.Btrue | Ast.Bfalse -> Ty.Bool

let fresh d = U (Uf.fresh d)
let new_ty n = fresh (Var n)
let arrow t1 t2 = fresh (Arrow (t1,t2))
let const c = fresh (Const c)

let union a b = Uf.union (fun a b -> a) a b

exception CannotUnify

let rec unify (U a) (U b) =
  if Uf.equal a b then ();
  match Uf.desc a, Uf.desc b with
  | Var n1, Var n2 -> 
      if n1 < n2 then union a b else union b a
  | Var _, _ -> union a b
  | _, Var _ -> union b a
  | Const c1, Const c2 when c1 = c2 -> union a b
  | Arrow (ta1,ta2), Arrow (tb1,tb2) -> 
      union a b;
      unify ta1 tb1;
      unify ta2 tb2
  | _, _ -> raise CannotUnify
      

let rec refresh_ty ~old ~new_ x =
  let rec aux' x =
    match Uf.desc x with
    | Var n when n > old -> Uf.fresh (Var new_)
    | Var _ -> x
    | (Const _) -> x
    | Arrow (t1,t2) -> 
        let t1' = aux t1 and t2' = aux t2 in
        if t1 == t1' && t2 == t2' then x
        else Uf.fresh (Arrow (t1,t2))
  and aux (U x) = U (aux' x) in
  aux x


let add_var env x t = { env with vars = VM.add x (env.n,t) env.vars }

let rec infer env t = function
  | Ast.App (e1,e2) ->
      let nt = new_ty env.n in
      infer env (arrow nt t) e1;
      infer env nt e2 
  | Ast.Var x ->
      begin try
        let m,xt = VM.find x env.vars in
        let t' = refresh_ty ~old:m ~new_:env.n xt in
        unify xt t'
      with Not_found -> 
        error (Misc.mysprintf "variable %a not found" Var.print x)
      end
  | Ast.Const c ->
      unify t (const (type_of_constant c))
  | Ast.Lam b ->
      let x, e = Ast.open_bind b in
      let nt = new_ty env.n in
      let nt2 = new_ty env.n in
      let () = unify (arrow nt nt2) t in
      let env = add_var env x nt in
      infer env nt2 e
  | Ast.Let (e1,b) ->
      let nt = new_ty env.n in
      infer {env with n = env.n + 1 } nt e1;
      let x,e2 = Ast.open_bind b in
      let env = add_var env x nt in
      infer env t e2

let infer e = 
  let nt = new_ty 0 in
  infer { vars = VM.empty; n = 0 } nt e


