module A = Clean_ast
open Unify
module SM = Misc.StringMap
module I = I_ast

type env = { vars : ((A.tvar list * A.rvar list * A.effvar list) * Ty.t) SM.t ;  }

exception Error of string

let error s = raise (Error s)

let add_var env x g t = { vars = SM.add x (g,t) env.vars }

let ymemo ff =
  let h = Hashtbl.create 17 in
  let rec f x =
    try Hashtbl.find h x
    with Not_found -> 
      let z = ff f x in
      Hashtbl.add h x z; z
  in
  f

let to_uf_node (tl,rl,el) x = 
  let bh f l = 
    let h = Hashtbl.create 3 in
    List.iter (fun x -> Hashtbl.add h x (f ())) l;
    h in
  let th = bh new_ty tl and rh = bh new_r rl and eh = bh new_e el in
  let rec aux' f = function
    | (Ty.Const c) -> const c
    | Ty.Arrow (t1,t2,e) -> arrow (f t1) (f t2) (eff e)
    | Ty.Tuple (t1,t2) -> tuple (f t1) (f t2)
    | Ty.Var x -> (try Hashtbl.find th x with Not_found -> var x)
    | Ty.Ref (r,t) -> ref_ (auxr r) (f t)
  and aux f (Ty.C x) = aux' f x 
  and auxr r = try Hashtbl.find rh r with Not_found -> mkr r 
  and auxe e = try Hashtbl.find eh e with Not_found -> mke e 
  and eff (rl,el) = 
    if SS.is_empty rl && SS.cardinal el = 1 then auxe (SS.choose el)
    else
      effect (SS.fold (fun x acc -> auxr x :: acc) rl []) 
        (SS.fold (fun x acc -> auxe x :: acc) el []) in 
  ymemo aux x, th,rh,eh

let rec infer' env t = function
  | A.App (e1,e2) ->
      let nt = new_ty () and e = new_e () in
      let e1 = infer env (arrow nt t e) e1 in
      let e2 = infer env nt e2 in
      I.App (e1,e2), Unify.effect [] [e;e1.I.e;e2.I.e]
  | A.Var x ->
      begin try
        let m,xt = SM.find x env.vars in
        let nt,tappl,rappl,eappl = to_uf_node m xt in
        unify nt t;
        I.Var (x, tappl, rappl, eappl), new_e ()
      with Not_found -> error (Misc.mysprintf "variable %s not found" x) end
  | A.Const c -> 
      unify t (const (Const.type_of_constant c));
      I.Const c, new_e ()
  | A.Lam (x,xt,e) ->
      let nt,_,_,_ = to_uf_node ([],[],[]) xt in
      let nt2 = new_ty () in
      let env = add_var env x ([],[],[]) xt in
      let e = infer env nt2 e in
      unify (arrow nt nt2 e.I.e) t;
      I.Lam (x,xt,e), new_e ()
  | A.Let (g,e1,x,e2) ->
      let nt = new_ty () in
      let e1 = infer env nt e1 in
      let xt = to_ty nt in
      let e2 = infer (add_var env x g xt) t e2 in
      I.Let (g,e1,x,e2), Unify.effect [] [e1.I.e; e2.I.e]
and infer env t e = 
  let e,eff = infer' env t e.A.v in
  { I.v = e ; t = t; e = eff }

let infer e = 
  let nt = new_ty () in
  infer { vars = Initial.typing_env } nt e
