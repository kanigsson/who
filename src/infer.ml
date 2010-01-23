open Ast
module SM = Misc.StringMap
module G = Ty.Generalize
module U = Unify

module S = Name.S
module AI = Ast.Infer
module PL = Predefined.Logic

type env = { 
  vars : (G.t * Ty.t) Name.M.t ;  
  types : (G.t * Ty.t option) Name.M.t;
  pm : bool;
  }

exception Error of string * Loc.loc

let error loc s = 
  Myformat.ksprintf (fun s -> raise (Error (s,loc))) s

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
    error loc "Inference: type mismatch between %a and %a" 
      U.print_node t1 U.print_node t2

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

let to_uf_node (tl,rl,evl) el (x : Ty.t ) = 
  let x = Ty.elsubst evl el x in
  let tn,th = bh U.new_ty tl and rn,rh = bh U.new_r rl in
  let rec aux' f x = 
    match x with
    | (Ty.Const c) -> Unify.const c
    | Ty.Arrow (t1,t2,e, c) -> 
        U.arrow (f t1) (f t2) (eff e) (List.map auxr c)
    | Ty.Tuple (t1,t2) -> U.tuple (f t1) (f t2)
    | Ty.Ref (r,t) -> U.ref_ (auxr r) (f t)
    | Ty.Map e -> U.map (eff e)
    | Ty.PureArr (t1,t2) -> U.parr (f t1) (f t2)
    | Ty.App (v,([],[],[])) -> 
        begin try HT.find th v with Not_found -> U.var v end
    | Ty.App (v,i) -> Unify.app v (Inst.map f auxr eff i) 
  and aux f (Ty.C x) : U.node = aux' f x 
  and real x = ymemo aux x
  and auxr r = try HT.find rh r with Not_found -> U.mkr r 
  and eff (ef : Effect.t) : U.effect =
    let rl, e = Effect.to_u_effect ef in
    List.map auxr rl, e in
  real x, (tn, rn, List.map eff el)

let to_uf_rnode r = U.mkr r
let to_uf_enode ef =
  let rl, e = Effect.to_u_effect ef in
  List.map to_uf_rnode rl, e

let sto_uf_node x = fst (to_uf_node G.empty [] x)

let to_logic_ty t = sto_uf_node (Ty.to_logic_type (U.to_ty t))

let pref eff cur (p : ParseT.t) = 
  Ast.ParseT.pure_lam cur (Ty.map (U.to_eff eff)) p p.loc

let postf eff t old cur res (p : ParseT.t) = 
  let et = Ty.map (U.to_eff eff) in
  let lam = Ast.ParseT.pure_lam in
  let lameff s = lam s et in
  lameff old (lameff cur (lam res (U.to_ty t) p p.loc ) p.loc) p.loc

module AP = Ast.ParseT
module Uf = Unionfind

let rec check_type env t x : Ast.Infer.t = 
  let e = infer env x in
  begin try U.unify t e.t
  with U.CannotUnify ->
    error e.loc "type error: term %a has type %a but expected type %a@."
      AI.print e U.print_node e.t U.print_node t
  end ; 
  e
and infer env (x : Ast.ParseT.t) : Ast.Infer.t = 
  let l = x.loc in
  let e,t,eff = 
    match x.v with
    (* special case for !! *)
    | App ({ v = App ({ v = Var (v,([],[],[])) }, ref,`Prefix,[]) }, 
      map, `Prefix, []) 
      when Name.equal v PL.get_var ->
        let map' = infer env map in
        let ref' = infer env ref in
        begin match Uf.desc map'.t, Uf.desc ref'.t with
        | U.T Ty.Map e, U.T Ty.Ref (r,_) ->
            let e = U.rremove e [r] in
            let e = U.to_eff e in
            let new_e = AP.app (AP.app (AP.var ~inst:[e] v l) ref l) map l in
            let e = infer env new_e in
            e.v, e.t, e.e
        | _ -> assert false
        end
    (* special case for restrict *)
    | App ({ v = Var (v,([],[],[e]))},m,`Prefix,[]) 
        when Name.equal v PL.restrict_var ->
          let map' = infer env m in
          begin match Uf.desc map'.t with
          | U.T Ty.Map em ->
              let em = U.to_eff em in
              let new_e = 
                AP.app (AP.var ~inst:[Effect.diff em e; e] v l) m l in
              let e = infer env new_e in
              e.v, e.t, e.e
          | _ -> assert false
          end
    | App (e1,e2, k, cap) ->
        let e1 = infer env e1 in
        let t1,t2, eff = 
          match Uf.desc e1.t with
          | U.T Ty.Arrow (t1,t2, eff, cap') -> 
              List.iter2 (fun a b -> U.runify a (to_uf_rnode b)) cap' cap; 
              t1,t2, eff
          | U.T Ty.PureArr (t1,t2) -> t1, t2, U.eff_empty
          | _ -> 
              error l "term %a is expected to be a function but is of type %a"
                AI.print e1 U.print_node e1.t
        in
        let e2 = check_type env t1 e2 in
        App (e1,e2,k, cap), t2, U.eff_union3 e1.e e2.e eff
    | Annot (e,t) ->
        let t' = sto_uf_node t in
        let e = check_type env t' e in
        Annot (e,t), t', e.e
    | Const c -> Const c, U.const (Const.type_of_constant c), U.eff_empty
    | PureFun (xt,(_,x,e)) ->
        let nt = sto_uf_node xt in
        let env = add_svar env x xt in
        let e = infer env e in
        PureFun (xt, Name.close_bind x e), U.parr nt e.t, U.eff_empty
    | Quant (k,xt,(_,x,e)) ->
        let env = add_svar env x xt in
        let e = check_type env U.prop e in
        Quant (k, xt, Name.close_bind x e), U.prop, U.eff_empty
    | LetReg (rl,e) -> 
        let e = infer env e in
        let eff = U.rremove e.e (List.map to_uf_rnode rl) in
        LetReg (rl,e), e.t, eff
    | Ite (e1,e2,e3) ->
        let e1 = check_type env U.bool e1 in
        let e2 = infer env e2 in
        let e3 = check_type env e2.t e3 in
        Ite (e1,e2,e3), e2.t, U.eff_union3 e1.e e2.e e3.e
    | Gen (g,e) ->
        let e = infer env e in
        Gen (g,e), e.t, e.e
    | Param (t,eff) -> 
        Param (t,eff), sto_uf_node t, to_uf_enode eff
    | For (dir,inv,i,s,e,body) ->
        let env = add_svar env i Ty.int in
        let body = check_type env U.unit body in
        let inv = pre env body.e inv l in
        For (dir, inv, i, s, e, body), U.unit, body.e
    | HoareTriple (p,f,x,q) ->
        let f' = infer {env with pm = false} f in
        begin match Uf.desc f'.t with
          | U.T Ty.Arrow (t1,t2,eff, _) -> 
              Format.printf "found HoareTriple of type %a@." U.print_node f'.t;
              let x = check_type env t1 x in
              let p = pre env eff p l in
              let q = post env eff t2 q l in
              HoareTriple  (p,infer env f,x,q), U.prop, U.eff_empty
          | _ -> 
              error l "term %a is not a function, but of type %a@."
              AI.print f' U.print_node f'.t
        end
    | Var (v,(_,_,el)) ->
(*         Myformat.printf "treating var: %a@." Name.print v; *)
        let (_,_,evl) as m ,xt = 
          try Name.M.find v env.vars
          with Not_found -> error l "variable %a not found" Name.print v in
        let xt = if env.pm then Ty.to_logic_type xt else xt in
        let nt,i = 
          try to_uf_node m el xt
          with Invalid_argument "List.fold_left2" ->
            error l "not the right number of effect vars: %a@.\
            I expected %d variables, but you gave %d effects.@." 
            Name.print v (List.length evl) (List.length el) in
(*         Myformat.printf "found type: %a@." U.print_node nt; *)
        Var (v, i), nt, U.eff_empty
    | Let (g,e1,(_,x,e2),r) ->
        let env, e1 = letgen env x g e1 r in
        let e2 = infer env e2 in
        Let (g, e1,Name.close_bind x e2,r), e2.t, U.eff_union e1.e e2.e
    | Lam (x,xt,cap,p,e,q) ->
        let nt = sto_uf_node xt in
        let env = add_svar env x xt in
        let e = infer {env with pm = false} e in
        let p = pre env e.e p l in
        let q = post env e.e e.t q l in
        Lam (x,xt,cap,p,e,q), U.arrow nt e.t e.e (List.map to_uf_rnode cap),
        U.eff_empty
  in
  { v = e ; t = t ; e  = eff ; loc = l }
and pre env eff (cur,x) l : AI.pre' = 
  let f = match x with
  | None -> ParseT.ptrue l
  | Some f -> f in
  cur, Some (check_type {env with pm = true} (base_pre_ty eff) (pref eff cur f))
and post env eff t (old,cur,x) l = 
  let t = to_logic_ty t in
  let bp = base_post_ty eff t in
  let r, f = 
    match x with
    | PNone -> Name.new_anon (), ParseT.ptrue l
    | PPlain f -> Name.new_anon (), f
    | PResult (r,f) -> r, f in
  old, cur, PPlain (check_type {env with pm = true} bp (postf eff t old cur r f))
and letgen env x g e r =
  let env' = 
    match r with
    | Const.NoRec | Const.LogicDef -> env
    | Const.Rec ty -> add_svar env x ty in
  let e = infer env' e in
  let xt = 
    try U.to_ty e.t 
    with Assert_failure _ -> 
      error e.loc "could not determine the type of: %a : %a@." Name.print x 
        U.print_node e.t in
  add_var env x g xt, e

let rec infer_th env d = 
  match d with
  | Formula (s,e,k) -> env, Formula (s,check_type env U.prop e, k)
  | Section (s,cl,dl) -> 
      let env, dl = 
        Misc.list_fold_map infer_th env dl in
      env, Section (s,cl,dl)
  | Logic (n,g,t) -> 
      let env = add_var env n g t in
(*       Myformat.printf "added: %a : %a@." Name.print n Ty.print t; *)
      env, Logic (n,g,t)
  | TypeDef (g,t,n) -> 
      let env = add_ty env n g t in
      env, TypeDef (g,t,n)
  | DLetReg rl -> env, DLetReg rl
  | Program (x,g,e,r) -> 
      let env,e = letgen env x g e r in
      env, Program (x,g,e,r)

let initial = { vars = Name.M.empty; pm = false; types = Name.M.empty; }
let infer_th th = 
  let _, dl = Misc.list_fold_map infer_th initial th in
  dl

module AR = Ast.Recon
open AR

let rec recon' = function
  | Var (x,i) -> Var (x,inst i)
  | Const c -> Const c
  | App (e1,e2,k,cap) -> App (recon e1, recon e2,k,cap)
  | PureFun (t,(s,x,e)) -> PureFun (t,(s,x, recon e))
  | Quant (k,t,(s,x,e)) -> Quant (k,t,(s,x, recon e))
  | Lam (x,ot,cap,p,e,q) -> 
      let e = recon e in
      Lam (x,ot, cap, pre p, e, post q)
  | Param (t,e) -> Param (t,e)
  | Let (g,e1,(_,x,e2),r) -> 
      Let (g, recon e1, Name.close_bind x (recon e2),r)
  | Ite (e1,e2,e3) -> Ite (recon e1, recon e2, recon e3)
  | For (dir,inv,i,st,en,body) ->
      let bdir = match dir with {Name.name = Some "forto"} -> true|_ -> false in
      let body = recon body in 
      let e = body.e and l = body.loc in
      let cur,inv = pre inv in
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
  | HoareTriple (p,f,x,q) -> 
      let f = recon f and x = recon x and p = get_pre p and q = get_post q in
      let l = f.loc in
      let _,t2, e = Ty.from_logic_tuple f.t in
      let f =
        effFA e (fun m -> effFA e (fun n -> forall t2 (fun r ->
          let lhs = impl (app p m l) (applist [AR.pre f l; x; m] l) l in
          let rhs = 
            impl (applist [AR.post f l; x; m ; n; r] l) (applist [q;m;n;r] l) l in
          and_ lhs rhs l) l) l) l in
      f.v
  | LetReg (vl,e) -> LetReg (vl,recon e)
  | Annot (e,t) -> Annot (recon e, t)
  | Gen (g,e) -> Gen (g,recon e)
and pre (cur,x) = 
  match x with
  | None ->  assert false
  | Some x -> cur, Some (recon x)
and get_pre (_,x) = 
  match x with
  | None -> assert false
  | Some x -> recon x
and get_post (_,_,x) =
  match x with
  | PPlain f -> recon f
  | _ -> assert false
and recon (t : Ast.Infer.t) : Ast.Recon.t = 
  { v = recon' t.v; t = U.to_ty t.t; e = U.to_eff t.e; loc = t.loc }
and inst i = Inst.map U.to_ty U.to_r U.to_eff i
and post (old,cur,x) =
  let p = match x with
  | PNone -> assert false
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
