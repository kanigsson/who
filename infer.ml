module A = Clean_ast
open Unify
module SM = Misc.StringMap

type env = { vars : (A.tvar list * Ty.t) SM.t ;  }

exception Error of string

let error s = raise (Error s)

let add_var env x tl t = { vars = SM.add x (tl,t) env.vars }

let ymemo ff =
  let h = Hashtbl.create 17 in
  let rec f x =
    try Hashtbl.find h x
    with Not_found -> 
      let z = ff f x in
      Hashtbl.add h x z; z
  in
  f

let to_uf_node tl x = 
  let rec aux' f = function
    | (Ty.Const c) -> const c
    | Ty.Arrow (t1,t2) -> arrow (f t1) (f t2)
    | Ty.Tuple (t1,t2) -> tuple (f t1) (f t2)
    | Ty.Var x when List.mem x tl -> new_ty ()
    | Ty.Var x -> var x
  and aux f (Ty.C x) = aux' f x in 
  ymemo aux x

let from_uf_node x = 
  let rec aux' = function
    | (Ty.Const c) -> Ty.const c
    | Ty.Arrow (t1,t2) -> Ty.arrow (aux t1) (aux t2)
    | Ty.Tuple (t1,t2) -> Ty.tuple (aux t1) (aux t2)
    | Ty.Var x -> Ty.var x
  and aux x = 
    match Uf.desc x with
    | U -> assert false
    | T t -> aux' t in
  aux x

let rec infer' env t = function
  | A.App (e1,e2) ->
      let nt = new_ty () in
      infer env (arrow nt t) e1;
      infer env nt e2
  | A.Var x ->
      begin try
        let m,xt = SM.find x env.vars in
        let nt = to_uf_node m xt in
        unify nt t
      with Not_found -> error (Misc.mysprintf "variable %s not found" x) end
  | A.Const c -> unify t (const (Const.type_of_constant c))
  | A.Lam (x,xt,e) ->
      let nt = to_uf_node [] xt in
      let nt2 = new_ty () in
      unify (arrow nt nt2) t;
      let env = add_var env x [] xt in
      infer env nt2 e
  | A.Let (tl,e1,x,e2) ->
      let nt = new_ty () in
      infer env nt e1;
      let xt = from_uf_node nt in
      infer (add_var env x tl xt) t e2
and infer env t e = 
  e.A.t <- t; 
  infer' env t e.A.v

let infer e = 
  let nt = new_ty () in
  infer { vars = Initial.typing_env } nt e
