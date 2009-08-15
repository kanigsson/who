open Unify
open Ast
module SM = Misc.StringMap
open Format

type env = { 
  vars : (Generalize.t * Ty.t) SM.t ;  
  types : (Generalize.t * Ty.t option) SM.t;
  pm : bool
  }

exception Error of string * Loc.loc

let error s loc = raise (Error (s,loc))

let add_var env x g t = { env with vars = SM.add x (g,t) env.vars }
let add_ty env x g t = { env with types = SM.add x (g,t) env.types }

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
    | (Ty.Const c) -> Unify.const c
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

let unify t1 t2 loc = 
  try unify t1 t2 
  with CannotUnify ->
    error 
      (Myformat.sprintf "type mismatch between %a and %a" 
        U.print_node t1 U.print_node t2) loc


let rec infer' env t loc = function
  | App (e1,e2) ->
      let nt = new_ty () and e = new_e () in
      let e1 = infer env (arrow nt t e) e1 in
      let e2 = infer env nt e2 in
      App (e1,e2), Unify.effect [] [e;e1.e;e2.e]
  | Var (x,_) -> 
      begin try
        let m,xt = SM.find x env.vars in
        let xt = if env.pm then to_logic_type xt else xt in
        let nt,i = to_uf_node m xt in
        unify nt t loc;
        Var (x, i), new_e ()
      with Not_found -> error (sprintf "variable %s not found" x) loc end
  | Const c -> 
      unify t (const (Const.type_of_constant c)) loc;
      Const c, new_e ()
  | PureFun (x,xt,e) ->
      let nt,_ = to_uf_node Generalize.empty xt in
      let nt' = new_ty () in
      let env = add_var env x Generalize.empty xt in
      let e = infer env nt' e in
      unify (parr nt nt') t loc;
      PureFun (x,xt,e), new_e ()
  | Lam (x,xt,p,e,q) ->
      let nt,_ = to_uf_node Generalize.empty xt in
      let nt' = new_ty () in
      let env = add_var env x Generalize.empty xt in
      let e = infer {env with pm = false} nt' e in
      unify (arrow nt nt' e.e) t loc;
      let p = 
        Misc.opt_map 
          (infer {env with pm = true} (parr (map e.e) (parr nt' prop))) p in
      let q = 
        Misc.opt_map 
          (infer {env with pm = true} (parr (map e.e) (parr nt' prop))) q in
      Lam (x,xt,p,e,q), new_e ()
  | TypeDef (g,t',x,e) -> 
      let env = add_ty env x g t' in
      let e = infer env t e in
      TypeDef (g,t',x,e), new_e ()
  | Let (g,e1,x,e2) ->
      let nt = new_ty () in
      let e1 = infer env nt e1 in
      let xt = to_ty nt in
      let e2 = infer (add_var env x g xt) t e2 in
      Let (g,e1,x,e2), Unify.effect [] [e1.e; e2.e]
  | Ite (e1,e2,e3) ->
      let e1 = infer env bool e1 in
      let e2 = infer env t e2 in
      let e3 = infer env t e3 in
      Ite (e1,e2,e3), Unify.effect [] [e1.e;e2.e; e3.e]
  | Axiom e -> Axiom (infer env prop e), new_e ()
  | Logic t' -> 
      let nt, _ = to_uf_node Generalize.empty t' in
      unify nt t loc; 
      Logic t', new_e ()
and infer env t (e : ParseT.t) : Ast.Infer.t = 
  let e',eff = infer' env t e.loc e.v in
  { v = e' ; t = t; e = eff; loc = e.loc }

let infer e = 
  let nt = new_ty () in
  infer { vars = Initial.typing_env; pm = false; types = SM.empty } nt e

let rec recon' = function
  | Var (x,i) -> Var (x,inst i)
  | Const c -> Const c
  | App (e1,e2) -> App (recon e1, recon e2)
  | PureFun (x,t,e) -> PureFun (x,t,recon e)
  | Lam (x,ot,p,e,q) -> 
      Lam (x,ot, Misc.opt_map recon p, recon e, Misc.opt_map recon q)
  | Let (g,e1,x,e2) -> Let (g, recon e1, x, recon e2)
  | Ite (e1,e2,e3) -> Ite (recon e1, recon e2, recon e3)
  | Axiom e -> Axiom (recon e)
  | Logic t -> Logic t
  | TypeDef (g,t,x,e) -> TypeDef (g,t,x,recon e)
and recon (t : Ast.Infer.t) : Ast.Recon.t = 
  { v = recon' t.v; t = U.to_ty t.t; e = U.to_eff t.e; loc = t.loc }
and inst (th,rh,eh) =
    List.map U.to_ty th, List.map U.to_r rh, List.map U.to_eff eh
