open Ast
module SM = Misc.StringMap
module G = Ty.Generalize
module U = Unify

module S = Name.S

type env = { 
  vars : (G.t * Ty.t) Name.M.t ;  
  types : (G.t * Ty.t option) Name.M.t;
  pm : bool;
  curloc : Loc.loc;
  }

exception Error of string * Loc.loc

let error s loc = raise (Error (s,loc))

let add_var env x g t = { env with vars = Name.M.add x (g,t) env.vars }
let add_svar env x t = add_var env x G.empty t
let add_ty env x g t = { env with types = Name.M.add x (g,t) env.types }

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
  try U.unify t1 t2 
  with U.CannotUnify ->
    error 
      (Myformat.sprintf "Inference: type mismatch between %a and %a" 
        U.print_node t1 U.print_node t2) loc

let bh f l = 
  let h = Hashtbl.create 3 in
  List.map (fun x -> let n = f () in Hashtbl.add h x n; n) l,h

let base_pre_ty eff = U.parr (U.map eff) U.prop
let base_post_ty eff t = 
  U.parr (U.map eff) (U.parr (U.map eff) (U.parr t U.prop)) 
let prety t eff = U.parr t (base_pre_ty eff)
let postty t eff t2 = U.parr t (base_post_ty eff t2)
let prepost_type t1 t2 e = U.tuple (prety t1 e) (postty t1 e t2)
let rlist_from_set_map f l = S.fold (fun x acc -> f x :: acc) l []
let elist_from_set_map f l = S.fold (fun x acc -> f x :: acc) l []

let to_uf_node (tl,rl,el) x = 
  let tn,th = bh U.new_ty tl and rn,rh = bh U.new_r rl 
  and en,eh = bh U.new_e el in
  let rec aux' f = function
    | (Ty.Const c) -> Unify.const c
    | Ty.Arrow (t1,t2,e) -> U.arrow (f t1) (f t2) (eff e)
    | Ty.Tuple (t1,t2) -> U.tuple (f t1) (f t2)
    | Ty.Var x -> (try HT.find th x with Not_found -> U.var x)
    | Ty.Ref (r,t) -> U.ref_ (auxr r) (f t)
    | Ty.Map e -> U.map (eff e)
    | Ty.PureArr (t1,t2) -> U.parr (f t1) (f t2)
    | Ty.App (v,i) -> Unify.app v (Inst.map f auxr eff i) 
  and aux f (Ty.C x) = aux' f x 
  and real x = ymemo aux x
  and auxr r = try HT.find rh r with Not_found -> U.mkr r
  and auxe e = try HT.find eh e with Not_found -> U.mke e 
  and eff (rl,el,cl) = 
    if S.is_empty rl && S.is_empty cl && S.cardinal el = 1 then 
      auxe (S.choose el)
    else
      U.effect (rlist_from_set_map auxr rl)
             (elist_from_set_map auxe el)
             (rlist_from_set_map auxr cl) in
  real x, (tn,rn,en)

let to_uf_enode (rl,el,cl) = 
    if S.is_empty rl && S.is_empty cl && S.cardinal el = 1 then 
      U.mke (S.choose el)
    else U.effect (rlist_from_set_map U.mkr rl)
             (elist_from_set_map U.mke el)
             (rlist_from_set_map U.mkr cl)

let sto_uf_node x = fst (to_uf_node G.empty x)

let to_logic_ty t = 
  sto_uf_node (Ty.to_logic_type (U.to_ty t))

let pref eff cur (p : ParseT.t) = 
  Ast.ParseT.pure_lam cur (Ty.map (U.to_eff eff)) p p.loc

let postf eff t old cur res (p : ParseT.t) = 
  let et = Ty.map (U.to_eff eff) in
  let lam = Ast.ParseT.pure_lam in
  let lameff s = lam s et in
  lameff old (lameff cur (lam res (U.to_ty t) p p.loc ) p.loc) p.loc

let rec infer' env t loc = function
  | App (e1,e2,k,cap) ->
      let nt = U.new_ty () 
      and e = if cap = [] then U.new_e () 
              else to_uf_enode (NEffect.from_cap_list cap) in
      let e1 = infer env (U.arrow nt t e) e1 in
      let e2 = infer env nt e2 in
      App (e1,e2,k,cap), Unify.effect [] [e;e1.e;e2.e] []
  | Annot (e,xt) -> 
      unify (sto_uf_node xt) t loc;
      let e = infer env t e in
      Annot (e,xt), e.e
  | Var (x,_) -> 
(*       Myformat.printf "var %a@." Vars.var x; *)
        let m,xt = 
          try Name.M.find x env.vars
          with Not_found -> 
            error (Myformat.sprintf "variable %a not found" Name.print x) loc in
        let xt = if env.pm then Ty.to_logic_type xt else xt in
        let nt,i = to_uf_node m xt in
        unify nt t loc;
        Var (x, i), U.new_e ()
  | Const c -> 
      unify t (U.const (Const.type_of_constant c)) loc;
      Const c, U.new_e ()
  | PureFun (xt,(_,x,e)) ->
      let nt = sto_uf_node xt in
      let nt' = U.new_ty () in
      let env = add_svar env x xt in
      let e = infer env nt' e in
      unify (U.parr nt nt') t loc;
      PureFun (xt,Name.close_bind x e), U.new_e ()
  | Quant (k,xt,(_,x,e)) ->
      let env = add_svar env x xt in
      let e = infer env t e in
      unify U.prop t loc;
      Quant (k,xt,Name.close_bind x e), U.new_e ()
  | Lam (x,xt,p,e,q) ->
      let nt = sto_uf_node xt in
      let nt' = U.new_ty () in
      let env = add_svar env x xt in
      let e = infer {env with pm = false} nt' e in
      unify (U.arrow nt nt' e.e ) t loc;
      let p = pre env e.e p in
      let q = post env e.e nt' q in
      Lam (x,xt,p,e,q), U.new_e ()
  | Param (t',e) -> 
      unify t (sto_uf_node t') loc;
      Param (t',e), to_uf_enode e
  | TypeDef (g,t',x,e) -> 
      let env = add_ty env x g t' in
      let e = infer env t e in
      TypeDef (g,t',x,e), U.new_e ()
  | Section (n,f,e) ->
      let e = infer env t e in
      Section (n,f,e), e.e
  | EndSec e -> 
      let e = infer env t e in
      EndSec e, e.e
  | Let (p,g,e1,(_,x,e2),r) ->
(*       Myformat.printf "infer-let: %a@." Name.print x; *)
      let nt = U.new_ty () in
      let env' = 
        match r with
        | NoRec -> env
        | Rec  ty -> (add_svar env x ty) in
      let e1 = infer env' nt e1 in
      let xt = try U.to_ty nt 
               with Assert_failure _ -> error (Name.to_string x) loc  in
      let e2 = infer (add_var env x g xt) t e2 in
      Let (p,g, e1,Name.close_bind x e2,r), 
      U.effect [] [e1.e; e2.e] []
  | Ite (e1,e2,e3) ->
      let e1 = infer env U.bool e1 in
      let e2 = infer env t e2 in
      let e3 = infer env t e3 in
      Ite (e1,e2,e3), U.effect [] [e1.e;e2.e; e3.e] []
  | Axiom e -> 
      unify U.prop t loc;
      Axiom (infer env U.prop e), U.new_e ()
  | For (dir,inv,i,s,e,body) ->
      unify t U.unit loc;
      let env = add_svar env i Ty.int in
      let body = infer env U.unit body in
      let inv = pre env body.e inv in
      For (dir,inv,i,s,e,body), body.e
  | Logic t' -> 
(*       Myformat.printf "logic: %a@." Ty.print t'; *)
      let nt = sto_uf_node t' in
      unify nt t loc; 
      Logic t', U.new_e ()
  | LetReg (vl,e) ->
      let e = infer env t e in
      let eff = NEffect.rremove vl (U.to_eff e.e) in
      LetReg (vl,e), to_uf_enode eff
  | Gen _ -> assert false

and infer env t (e : ParseT.t) : Ast.Infer.t = 
  let e',eff = infer' {env with curloc = e.loc} t e.loc e.v in
  { v = e' ; t = t; e = eff; loc = e.loc }
and pre env eff (cur,x) = 
  let p = match x with
  | None -> None
  | Some f -> 
      Some (infer {env with pm = true} (base_pre_ty eff) (pref eff cur f))
  in cur, p
and post env eff t (old,cur,x) = 
  let p = match x with
  | PNone -> PNone
  | PPlain f -> 
      let t = to_logic_ty t in
      PPlain (infer {env with pm = true} (base_post_ty eff t) 
        (postf eff t old cur (Name.new_anon ()) f))
  | PResult (r,f) ->
      let t = to_logic_ty t in
      PPlain (infer {env with pm = true} (base_post_ty eff t) 
        (postf eff t old cur r f)) in
  old,cur,p

let initial = { vars = Name.M.empty; pm = false; 
                types = Name.M.empty; curloc = Loc.dummy; }
let infer e = 
  let nt = U.new_ty () in
  infer initial nt e

open Recon
let rec recon' = function
  | Var (x,i) -> Var (x,inst i)
  | Const c -> Const c
  | App (e1,e2,k,cap) -> App (recon e1, recon e2,k,cap)
  | PureFun (t,(s,x,e)) -> PureFun (t,(s,x, recon e))
  | Quant (k,t,(s,x,e)) -> Quant (k,t,(s,x, recon e))
  | Lam (x,ot,p,e,q) -> 
      Lam (x,ot, pre p, recon e, post q)
  | Param (t,e) -> Param (t,e)
  | Let (p,g,e1,(_,x,e2),r) -> 
      Let (p,g, recon e1, Name.close_bind x (recon e2),r)
  | Ite (e1,e2,e3) -> Ite (recon e1, recon e2, recon e3)
  | Axiom e -> Axiom (recon e)
  | Logic t -> Logic t
  | TypeDef (g,t,x,e) -> TypeDef (g,t,x,recon e)
  | For (dir,inv,i,st,en,body) ->
      let bdir = match dir with {Name.name = Some "forto"} -> true|_ -> false in
      let cur,inv = pre inv and body = recon body in
      let e = body.e and l = body.loc in
      let inv = match inv with | None -> ptrue_ l | Some f -> f in
      let inv' = plam i Ty.int inv l in
      let intvar s = svar s Ty.int l in
      let curvar = svar cur (Ty.map e) l in
      let sv = intvar st and ev = intvar en and iv = intvar i in
      let pre = 
        if bdir then
        (* forto: λcur. start <= i /\ i <= end_ /\ inv *)
          efflam cur e (and_ (encl sv iv ev l) (app inv curvar l) l) l
        else
        (* fordownto: λcur. end_ <= i /\ i <= start /\ inv *)
          efflam cur e (and_ (encl ev iv sv l) (app inv curvar l) l) l in
      let old = Name.new_anon () in
      let post = 
        let next = if bdir then succ iv l else prev iv l in
        (* forto : λold.λcurλ(). inv (i+1) cur *)
        (* fordownto : λold.λcurλ(). inv (i-1) cur *)
        efflam old e
          (efflam cur e
            (plam (Name.new_anon ()) Ty.unit
              (app2 inv' next curvar l) l) l) l in
      let bodyfun = lam i Ty.int (cur,Some pre) body (old,cur,PPlain post) l in
      (* forvar inv start end bodyfun *)
      (app2 (app2 (var dir ([],[],[e]) Ty.forty l) inv' sv l) ev bodyfun l).v
  | LetReg (vl,e) -> LetReg (vl,recon e)
  | Annot (e,t) -> Annot (recon e, t)
  | Section (n,f,e) -> Section (n,f,recon e)
  | EndSec e -> EndSec (recon e)
  | Gen _ -> assert false
and pre (cur,x) = cur, Misc.opt_map recon x
and recon (t : Ast.Infer.t) : Ast.Recon.t = 
  { v = recon' t.v; t = U.to_ty t.t; e = U.to_eff t.e; loc = t.loc }
and inst (th,rh,eh) =
    List.map U.to_ty th, List.map U.to_r rh, List.map U.to_eff eh
and post (old,cur,x) =
  let p = match x with
  | PNone -> PNone
  | PPlain f -> PPlain (recon f)
  | _ -> assert false in
  old, cur, p
