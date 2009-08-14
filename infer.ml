module A = Clean_ast
open Unify
module SM = Misc.StringMap
module I = I_ast
open Format

type env = { 
  vars : (Generalize.t * Ty.t) SM.t ;  
  pm : bool
  }

exception Error of string

let error s = raise (Error s)

let add_var env x g t = { env with vars = SM.add x (g,t) env.vars }

let ymemo ff =
  let h = Hashtbl.create 17 in
  let rec f x =
    try Hashtbl.find h x
    with Not_found -> 
      let z = ff f x in
      Hashtbl.add h x z; z in
  f

let to_uf_node (tl,rl,el) x = 
  let bh f l = 
    let h = Hashtbl.create 3 in
    List.map (fun x -> let n = f () in Hashtbl.add h x n; n) l,h in
  let tn,th = bh new_ty tl and rn,rh = bh new_r rl and en,eh = bh new_e el in
  let rec aux' f = function
    | (Ty.Const c) -> const c
    | Ty.Arrow (t1,t2,e) -> arrow (f t1) (f t2) (eff e)
    | Ty.Tuple (t1,t2) -> tuple (f t1) (f t2)
    | Ty.Var x -> (try Hashtbl.find th x with Not_found -> var x)
    | Ty.Ref (r,t) -> ref_ (auxr r) (f t)
    | Ty.Map e -> map (eff e)
    | Ty.PureArr (t1,t2) -> parr (f t1) (f t2)
  and aux f (Ty.C x) = aux' f x 
  and auxr r = try Hashtbl.find rh r with Not_found -> mkr r 
  and auxe e = try Hashtbl.find eh e with Not_found -> mke e 
  and eff (rl,el) = 
    if SS.is_empty rl && SS.cardinal el = 1 then auxe (SS.choose el)
    else
      effect (SS.fold (fun x acc -> auxr x :: acc) rl []) 
        (SS.fold (fun x acc -> auxe x :: acc) el []) in 
  ymemo aux x, (tn,rn,en)

let to_logic_type t = 
  let rec aux' = function
    | (Ty.Var _ | Ty.Const _ | Ty.Map _) as t -> Ty.C t
    | Ty.Tuple (t1,t2) -> Ty.tuple (aux t1) (aux t2)
    | Ty.PureArr (t1,t2) -> Ty.parr (aux t1) (aux t2)
    | Ty.Arrow (t1,t2,e) -> 
        Ty.tuple (Ty.parr t1 (Ty.parr (Ty.map e) (Ty.prop)))
          (Ty.parr (Ty.map e) (Ty.parr t2 (Ty.prop)))
    | Ty.Ref _ -> Ty.unit
  and aux (Ty.C x) = aux' x in
  aux t


let rec infer' env t = function
  | A.App (e1,e2) ->
      let nt = new_ty () and e = new_e () in
      let e1 = infer env (arrow nt t e) e1 in
      let e2 = infer env nt e2 in
      I.App (e1,e2), Unify.effect [] [e;e1.I.e;e2.I.e]
  | A.Var x -> 
      begin try
        let m,xt = SM.find x env.vars in
(*         printf "var %s : %a@." x Ty.print xt; *)
        let xt = if env.pm then to_logic_type xt else xt in
        let nt,i = to_uf_node m xt in
        unify nt t;
        I.Var (x, i), new_e ()
      with Not_found -> error (sprintf "variable %s not found" x) end
  | A.Const c -> 
      unify t (const (Const.type_of_constant c));
      I.Const c, new_e ()
  | A.Lam (x,xt,e,p) ->
      let nt,_ = to_uf_node Generalize.empty xt in
      let nt' = new_ty () in
      let env = add_var env x Generalize.empty xt in
      let e = infer env nt' e in
      unify (arrow nt nt' e.I.e) t;
      let p = 
        match p with
        | None -> None
        | Some p ->
          Some (infer {env with pm = true} 
                   (parr (map e.I.e) (parr nt' prop)) p) in
      I.Lam (x,xt,e,p), new_e ()
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
  infer { vars = Initial.typing_env; pm = false } nt e
