open Unify
open Ast
module SM = Misc.StringMap
open Format

type env = { 
  vars : (Ty.Generalize.t * Ty.t) SM.t ;  
  types : (Ty.Generalize.t * Ty.t option) SM.t;
  pm : bool;
  curloc : Loc.loc;
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

module HT = Hashtbl

let unify t1 t2 loc = 
  try unify t1 t2 
  with CannotUnify ->
    error 
      (Myformat.sprintf "type mismatch between %a and %a" 
        U.print_node t1 U.print_node t2) loc

let bh f l = 
  let h = Hashtbl.create 3 in
  List.map (fun x -> let n = f () in Hashtbl.add h x n; n) l,h

let prety eff = parr (map eff) prop
let postty eff t = parr (map eff) (parr (map eff) (parr t prop)) 

let to_uf_node (tl,rl,el) x = 
  let tn,th = bh new_ty tl and rn,rh = bh new_r rl and en,eh = bh new_e el in
  let rec aux' f = function
    | (Ty.Const c) -> Unify.const c
    | Ty.Arrow (t1,t2,e) -> arrow (f t1) (f t2) (eff e)
    | Ty.Tuple (t1,t2) -> tuple (f t1) (f t2)
    | Ty.Var x -> (try HT.find th x with Not_found -> var x)
    | Ty.Ref (r,t) -> ref_ (auxr r) (f t)
    | Ty.Map e -> map (eff e)
    | Ty.PureArr (t1,t2) -> parr (f t1) (f t2)
    | Ty.App (v,i) -> Unify.app v (Inst.map real auxr eff i) 
  and aux f (Ty.C x) = aux' f x 
  and real x = ymemo aux x
  and auxr r = try HT.find rh r with Not_found -> mkr r
  and auxe e = try HT.find eh e with Not_found -> mke e 
  and eff (rl,el) = 
    if SS.is_empty rl && SS.cardinal el = 1 then auxe (SS.choose el)
    else
      effect (SS.fold (fun x acc -> auxr x :: acc) rl []) 
        (SS.fold (fun x acc -> auxe x :: acc) el []) in 
  real x, (tn,rn,en)

let pref eff (p : ParseT.t) = 
  Ast.ParseT.pure_lam "cur" (Ty.map (to_eff eff)) p p.loc

let postf eff t res (p : ParseT.t) = 
  let et = Ty.map (to_eff eff) in
  let lam = Ast.ParseT.pure_lam in
  let lameff s = lam s et in
  lameff "old" (lameff "cur" (lam res (to_ty t) p p.loc ) p.loc) p.loc

let rec infer' env t loc = function
  | App (e1,e2) ->
      let nt = new_ty () and e = new_e () in
      let e1 = infer env (arrow nt t e) e1 in
      let e2 = infer env nt e2 in
      App (e1,e2), Unify.effect [] [e;e1.e;e2.e]
  | Var (x,_) -> 
(*       Myformat.printf "var %a@." Vars.var x; *)
        let m,xt = 
          try SM.find x env.vars
          with Not_found -> error (sprintf "variable %s not found" x) loc in
        let xt = if env.pm then Ty.to_logic_type xt else xt in
        let nt,i = to_uf_node m xt in
        unify nt t loc;
        Var (x, i), new_e ()
  | Const c -> 
      unify t (const (Const.type_of_constant c)) loc;
      Const c, new_e ()
  | PureFun (x,xt,e) ->
      let nt,_ = to_uf_node Ty.Generalize.empty xt in
      let nt' = new_ty () in
      let env = add_var env x Ty.Generalize.empty xt in
      let e = infer env nt' e in
      unify (parr nt nt') t loc;
      PureFun (x,xt,e), new_e ()
  | Quant (k,x,xt,e) ->
      let env = add_var env x Ty.Generalize.empty xt in
      let e = infer env t e in
      unify prop t loc;
      Quant (k,x,xt,e), new_e ()
  | Lam (x,xt,p,e,q) ->
      let nt,_ = to_uf_node Ty.Generalize.empty xt in
      let nt' = new_ty () in
      let env = add_var env x Ty.Generalize.empty xt in
      let e = infer {env with pm = false} nt' e in
      unify (arrow nt nt' e.e) t loc;
      let p = pre env e.e p in
      let q = post env e.e nt' q in
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
  | Axiom e -> 
      unify prop t loc;
      Axiom (infer env prop e), new_e ()
  | Logic t' -> 
      let nt, _ = to_uf_node Ty.Generalize.empty t' in
      unify nt t loc; 
      Logic t', new_e ()

and infer env t (e : ParseT.t) : Ast.Infer.t = 
  let e',eff = infer' {env with curloc = e.loc} t e.loc e.v in
  { v = e' ; t = t; e = eff; loc = e.loc }
and pre env eff = function
  | None -> None
  | Some f -> Some (infer {env with pm = true} (prety eff) (pref eff f))
and post env eff t = function
  | PNone -> PNone
  | PPlain f -> 
      PPlain (infer {env with pm = true} (postty eff t) (postf eff t "" f))
  | PResult (r,f) ->
      PPlain (infer {env with pm = true} (postty eff t) (postf eff t r f))

let initial = { vars = Initial.typing_env; pm = false; 
                types = SM.empty; curloc = Loc.dummy; }
let infer e = 
  let nt = new_ty () in
  infer initial nt e

let rec recon' = function
  | Var (x,i) -> Var (x,inst i)
  | Const c -> Const c
  | App (e1,e2) -> App (recon e1, recon e2)
  | PureFun (x,t,e) -> PureFun (x,t,recon e)
  | Quant (k,x,t,e) -> Quant (k,x,t,recon e)
  | Lam (x,ot,p,e,q) -> 
      Lam (x,ot, Misc.opt_map recon p, recon e, post q)
  | Let (g,e1,x,e2) -> Let (g, recon e1, x, recon e2)
  | Ite (e1,e2,e3) -> Ite (recon e1, recon e2, recon e3)
  | Axiom e -> Axiom (recon e)
  | Logic t -> Logic t
  | TypeDef (g,t,x,e) -> TypeDef (g,t,x,recon e)
and recon (t : Ast.Infer.t) : Ast.Recon.t = 
  { v = recon' t.v; t = U.to_ty t.t; e = U.to_eff t.e; loc = t.loc }
and inst (th,rh,eh) =
    List.map U.to_ty th, List.map U.to_r rh, List.map U.to_eff eh
and post = function
  | PNone -> PNone
  | PPlain f -> PPlain (recon f)
  | _ -> assert false
