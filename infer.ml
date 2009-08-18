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
let add_svar env x t = add_var env x Ty.Generalize.empty t
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

let list_from_set_map f l = SS.fold (fun x acc -> f x :: acc) l []

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
    | Ty.App (v,i) -> Unify.app v (Inst.map f auxr eff i) 
  and aux f (Ty.C x) = aux' f x 
  and real x = ymemo aux x
  and auxr r = try HT.find rh r with Not_found -> mkr r
  and auxe e = try HT.find eh e with Not_found -> mke e 
  and eff (rl,el,cl) = 
    if SS.is_empty rl && SS.is_empty cl && SS.cardinal el = 1 then 
      auxe (SS.choose el)
    else
      effect (list_from_set_map auxr rl)
             (list_from_set_map auxe el)
             (list_from_set_map auxr cl) in
  real x, (tn,rn,en)

let to_uf_enode (rl,el,cl) = 
    if SS.is_empty rl && SS.is_empty cl && SS.cardinal el = 1 then 
      mke (SS.choose el)
    else
      effect (list_from_set_map mkr rl)
             (list_from_set_map mke el)
             (list_from_set_map mkr cl)

let sto_uf_node x = fst (to_uf_node Ty.Generalize.empty x)

let pref eff (p : ParseT.t) = 
  Ast.ParseT.pure_lam "cur" (Ty.map (to_eff eff)) p p.loc

let postf eff t res (p : ParseT.t) = 
  let et = Ty.map (to_eff eff) in
  let lam = Ast.ParseT.pure_lam in
  let lameff s = lam s et in
  lameff "old" (lameff "cur" (lam res (to_ty t) p p.loc ) p.loc) p.loc

let rec infer' env t loc = function
  | App (e1,e2,k,cap) ->
      let nt = new_ty () 
      and e = if cap = [] then new_e () 
              else to_uf_enode (Effect.from_cap_list cap) in
      let e1 = infer env (arrow nt t e) e1 in
      let e2 = infer env nt e2 in
      App (e1,e2,k,cap), Unify.effect [] [e;e1.e;e2.e] []
  | Annot (e,xt) -> 
      unify (sto_uf_node xt) t loc;
      let e = infer env t e in
      Annot (e,xt), e.e
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
      let nt = sto_uf_node xt in
      let nt' = new_ty () in
      let env = add_svar env x xt in
      let e = infer env nt' e in
      unify (parr nt nt') t loc;
      PureFun (x,xt,e), new_e ()
  | Quant (k,x,xt,e) ->
      let env = add_svar env x xt in
      let e = infer env t e in
      unify prop t loc;
      Quant (k,x,xt,e), new_e ()
  | Lam (x,xt,p,e,q) ->
      let nt = sto_uf_node xt in
      let nt' = new_ty () in
      let env = add_svar env x xt in
      let e = infer {env with pm = false} nt' e in
      unify (arrow nt nt' e.e ) t loc;
      let p = pre env e.e p in
      let q = post env e.e nt' q in
      Lam (x,xt,p,e,q), new_e ()
  | Param (t',e) -> 
      unify t (sto_uf_node t') loc;
      Param (t',e), to_uf_enode e
  | TypeDef (g,t',x,e) -> 
      let env = add_ty env x g t' in
      let e = infer env t e in
      TypeDef (g,t',x,e), new_e ()
  | Let (g,e1,x,e2,r) ->
      let nt = new_ty () in
      let env' = 
        match r with
        | NoRec -> env
        | Rec  ty -> (add_svar env x ty) in
      let e1 = infer env' nt e1 in
      let xt = try to_ty nt with Assert_failure _ -> error x loc  in
      let e2 = infer (add_var env x g xt) t e2 in
      Let (g,e1,x,e2,r), Unify.effect [] [e1.e; e2.e] []
  | Ite (e1,e2,e3) ->
      let e1 = infer env bool e1 in
      let e2 = infer env t e2 in
      let e3 = infer env t e3 in
      Ite (e1,e2,e3), Unify.effect [] [e1.e;e2.e; e3.e] []
  | Axiom e -> 
      unify prop t loc;
      Axiom (infer env prop e), new_e ()
  | For (dir,inv,i,body) ->
      unify t unit loc;
      let env = add_svar env i Ty.int in
      let body = infer env unit body in
      let inv = pre env body.e inv in
      For (dir,inv,i,body), body.e
  | Logic t' -> 
      let nt = sto_uf_node t' in
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

let initial = { vars = SM.empty; pm = false; 
                types = SM.empty; curloc = Loc.dummy; }
let infer e = 
  let nt = new_ty () in
  infer initial nt e

open Recon
let rec recon' = function
  | Var (x,i) -> Var (x,inst i)
  | Const c -> Const c
  | App (e1,e2,k,cap) -> App (recon e1, recon e2,k,cap)
  | PureFun (x,t,e) -> PureFun (x,t,recon e)
  | Quant (k,x,t,e) -> Quant (k,x,t,recon e)
  | Lam (x,ot,p,e,q) -> 
      Lam (x,ot, Misc.opt_map recon p, recon e, post q)
  | Param (t,e) -> Param (t,e)
  | Let (g,e1,x,e2,r) -> Let (g, recon e1, x, recon e2,r)
  | Ite (e1,e2,e3) -> Ite (recon e1, recon e2, recon e3)
  | Axiom e -> Axiom (recon e)
  | Logic t -> Logic t
  | TypeDef (g,t,x,e) -> TypeDef (g,t,x,recon e)
  | For (dir,inv,i,body) ->
      let inv = Misc.opt_map recon inv and body = recon body in
      let e = body.e and l = body.loc in
      let inv = match inv with | None -> ptrue_ l | Some f -> f in
      let inv' = plam "i" Ty.int inv l in
      let intvar s = svar s Ty.int l in
      let curvar = svar "cur" (Ty.map e) l in
      let sv = intvar "%%start" and ev = intvar "%%end_" and iv = intvar i in
      let pre = 
        (* pre : λcur. start <= i /\ i <= end_ /\ inv *)
          efflam "cur" e (and_ (encl sv iv ev l) (app inv curvar l) l) l in
      let post = 
        (* post : λold.λcurλ(). inv (i+1) cur *)
        efflam "old" e
          (efflam "cur" e
            (plam "%%anon" Ty.unit
              (app2 inv' (succ iv l) curvar l) l) l) l in
      let bodyfun = lam "i" Ty.int (Some pre) body (PPlain post) l in
      (* forvar inv start end bodyfun *)
      (app2 (app2 (var dir ([],[],[e]) Ty.forty l) inv' sv l) ev bodyfun l).v
  | Annot (e,t) -> Annot (recon e, t)
and recon (t : Ast.Infer.t) : Ast.Recon.t = 
  { v = recon' t.v; t = U.to_ty t.t; e = U.to_eff t.e; loc = t.loc }
and inst (th,rh,eh) =
    List.map U.to_ty th, List.map U.to_r rh, List.map U.to_eff eh
and post = function
  | PNone -> PNone
  | PPlain f -> PPlain (recon f)
  | _ -> assert false
