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

exception FindFirst of Name.t

let to_uf_node (tl,rl,el) x = 
  let tn,th = bh U.new_ty tl and rn,rh = bh U.new_r rl 
  and en,eh = bh U.new_e el in
  let rec aux' f = function
    | (Ty.Const c) -> Unify.const c
    | Ty.Arrow (t1,t2,e, c) -> 
        U.arrow (f t1) (f t2) (eff e) (List.map auxr c)
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
  and eff eff = 
    (* We need a single effect variable here *)
      (* We are lucky, the effect is in fact a single effect var *)
    if NEffect.is_esingleton eff then auxe (NEffect.e_choose eff)
    (* or in fact there is no effect var, also ok *)
    else if NEffect.no_effvar eff then 
      let rl = NEffect.to_rlist eff in
      U.effect (List.map auxr rl) []
    else
      (* try to find an unquantified effect var *)
      try 
        NEffect.eiter (fun z -> 
          try ignore (HT.find eh z);() with Not_found -> raise (FindFirst z)) eff;
        (* we have not found one *)
        (* We simply choose one and add the others as constraints *)
        let e = NEffect.e_choose eff in
        let en = HT.find eh e in
        let eff = NEffect.eremove eff e in
        let rl, el = NEffect.to_lists eff in
        let en' = U.effect (List.map auxr rl) (List.map auxe el) in
        U.eunify en en'; en
      with FindFirst e ->
        let eff = NEffect.eremove eff e in
        let rl, el = NEffect.to_lists eff in
        U.effect ~name:e (List.map auxr rl) (List.map auxe el) in
  real x, (tn,rn,en)

let to_uf_rnode r = U.mkr r
let to_uf_enode eff = 
  if NEffect.is_esingleton eff then U.mke (NEffect.e_choose eff)
  else 
    let rl, el = NEffect.to_lists eff in
    U.effect (List.map U.mkr rl) (List.map U.mke el)

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

let rec infer' env t loc x = 
  match x with
  | App (e1,e2,k,cap) ->
      let nt = U.new_ty () and e = U.new_e () in
      let e1 = infer env (U.arrow nt t e (List.map to_uf_rnode cap)) e1 in
      let e2 = infer env nt e2 in
      App (e1,e2,k,cap), Unify.effect [] [e;e1.e;e2.e]
  | Annot (e,xt) -> 
      unify (sto_uf_node xt) t loc;
      let e = infer env t e in
      Annot (e,xt), e.e
  | Var (x,_) -> 
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
  | Lam (x,xt,cap,p,e,q) ->
      let nt = sto_uf_node xt in
      let nt' = U.new_ty () in
      let env = add_svar env x xt in
      let e = infer {env with pm = false} nt' e in
      unify (U.arrow nt nt' e.e (List.map to_uf_rnode cap)) t loc;
      let p = pre env e.e p in
      let q = post env e.e nt' q in
      Myformat.printf "closing lambda : %a @." Name.print x;
      Lam (x,xt,cap,p,e,q), U.new_e ()
  | Param (t',e) -> 
      unify t (sto_uf_node t') loc;
      Param (t',e), to_uf_enode e
  | Let (g,e1,(_,x,e2),r) ->
      let env, e1 = letgen env x g e1 r in
      let e2 = infer env t e2 in
      Let (g, e1,Name.close_bind x e2,r), 
      U.effect [] [e1.e; e2.e]
  | Ite (e1,e2,e3) ->
      let e1 = infer env U.bool e1 in
      let e2 = infer env t e2 in
      let e3 = infer env t e3 in
      Ite (e1,e2,e3), U.effect [] [e1.e;e2.e; e3.e]
  | For (dir,inv,i,s,e,body) ->
      unify t U.unit loc;
      let env = add_svar env i Ty.int in
      let body = infer env U.unit body in
      let inv = pre env body.e inv in
      For (dir,inv,i,s,e,body), body.e
  | LetReg (vl,e) ->
      let e = infer env t e in
      let eff = NEffect.rremove (U.to_eff e.e) vl in
      LetReg (vl,e), to_uf_enode eff
  | Gen (g,e) -> 
      let e = infer env t e in
      Gen (g,e), e.e

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
      let bp = base_post_ty eff t in
      let pf = postf eff t old cur (Name.new_anon ()) f in
      let r = PPlain (infer {env with pm = true} bp pf) in
      r
  | PResult (r,f) ->
      let t = to_logic_ty t in
      PPlain (infer {env with pm = true} (base_post_ty eff t) 
        (postf eff t old cur r f)) in
  old,cur,p

and letgen env x g e r =
  let nt = U.new_ty () in
  let env' = 
    match r with
    | NoRec -> env
    | Rec  ty -> (add_svar env x ty) in
  let e = infer env' nt e in
  let xt = 
    try U.to_ty nt 
    with Assert_failure _ -> 
      error (Myformat.sprintf "%a: %a@." Name.print x U.print_node nt) e.loc in
  add_var env x g xt, e

let rec infer_th env d = 
  match d with
  | Formula (s,e,k) -> env, Formula (s,infer env U.prop e, k)
  | Section (s,cl,dl) -> 
      let env, dl = 
        Misc.list_fold_map infer_th env dl in
      env, Section (s,cl,dl)
  | Logic (n,g,t) -> 
      let env = add_var env n g t in
      env, Logic (n,g,t)
  | TypeDef (g,t,n) -> 
      let env = add_ty env n g t in
      env, TypeDef (g,t,n)
  | DLetReg rl -> env, DLetReg rl
  | Program (x,g,e,r) -> 
      let env,e = letgen env x g e r in
      Myformat.printf "found %a : %a@." Name.print x U.print_node e.t;
      env, Program (x,g,e,r)

let initial = { vars = Name.M.empty; pm = false; 
                types = Name.M.empty; curloc = Loc.dummy; }
let infer_th th = 
  let _, dl = Misc.list_fold_map infer_th initial th in
  dl

open Recon
let rec recon' = function
  | Var (x,i) -> Var (x,inst i)
  | Const c -> Const c
  | App (e1,e2,k,cap) -> App (recon e1, recon e2,k,cap)
  | PureFun (t,(s,x,e)) -> PureFun (t,(s,x, recon e))
  | Quant (k,t,(s,x,e)) -> Quant (k,t,(s,x, recon e))
  | Lam (x,ot,cap,p,e,q) -> 
      let e = recon e in
      Lam (x,ot, cap, pre e.e p e.loc, e, post e.e e.t q e.loc)
  | Param (t,e) -> Param (t,e)
  | Let (g,e1,(_,x,e2),r) -> 
      Let (g, recon e1, Name.close_bind x (recon e2),r)
  | Ite (e1,e2,e3) -> Ite (recon e1, recon e2, recon e3)
  | For (dir,inv,i,st,en,body) ->
      let bdir = match dir with {Name.name = Some "forto"} -> true|_ -> false in
      let body = recon body in 
      let e = body.e and l = body.loc in
      let cur,inv = pre e inv l in
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
  | Gen (g,e) -> Gen (g,recon e)
and pre eff (cur,x) loc = 
  match x with
  | None -> cur, Some (efflamho eff (fun _ -> ptrue_ loc) loc)
  | Some x -> cur, Some (recon x)
and recon (t : Ast.Infer.t) : Ast.Recon.t = 
  { v = recon' t.v; t = U.to_ty t.t; e = U.to_eff t.e; loc = t.loc }
and inst (th,rh,eh) =
    List.map U.to_ty th, List.map U.to_r rh, List.map U.to_eff eh
and post eff t (old,cur,x) loc =
  let p = match x with
  | PNone -> 
      PPlain (efflamho eff (fun _ -> efflamho eff (fun _ ->
                plamho t (fun _ -> ptrue_ loc) loc) loc) loc)
  | PPlain f -> PPlain (recon f)
  | _ -> assert false in
  old, cur, p

let rec recon_decl x = 
  match x with
  | Logic (x,g,t) -> Logic (x,g,t)
  | Formula (s,t,k) -> Formula (s, recon t, k)
  | Section (s,cl, dl) -> Section (s,cl, recon_th dl)
  | DLetReg rl -> DLetReg rl
  | TypeDef (g,t,n) -> TypeDef (g,t,n)
  | Program (n,g,t,r) -> Program (n,g,recon t, r)
and recon_th l = List.map recon_decl l
