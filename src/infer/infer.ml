(******************************************************************************)
(*                                                                            *)
(*                      Who                                                   *)
(*                                                                            *)
(*       A simple VCGen for higher-order programs.                            *)
(*                                                                            *)
(*  Copyright (C) 2009, 2010, Johannes Kanig                                  *)
(*  Contact: kanig@lri.fr                                                     *)
(*                                                                            *)
(*  Who is free software: you can redistribute it and/or modify it under the  *)
(*  terms of the GNU Lesser General Public License as published by the Free   *)
(*  Software Foundation, either version 3 of the License, or any later        *)
(*  version.                                                                  *)
(*                                                                            *)
(*  Who is distributed in the hope that it will be useful, but WITHOUT ANY    *)
(*  WARRANTY; without even the implied warranty of MERCHANTABILITY or         *)
(*  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public      *)
(*  License for more details.                                                 *)
(*                                                                            *)
(*  You should have received a copy of the GNU Lesser General Public License  *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>      *)
(******************************************************************************)

module I = InternalParseTree
open InferTree
module PI = Identifiers
module M = MutableType
module SM = Misc.StringMap
module G = Ty.Generalize
module U = Unify

module S = Name.S
module PL = Predefined

module Env : sig
  type t

  val empty : t

  val add_var : t -> Name.t -> G.t -> M.t -> t
  val add_svar : t -> Name.t -> M.t -> t

  val lookup : t -> Name.t -> G.t * M.t

  val to_logic_env : t -> t
  val to_program_env : t -> t
  val is_logic_env : t -> bool

  val has_binding : t -> Name.t -> bool

end = struct
  type t = { vars : (G.t * M.t) Name.M.t ; pm : bool; }

  let empty = { vars = Name.M.empty; pm = false; }
  let add_var env x g t =
    { env with vars = Name.M.add x (g,t) env.vars }
  let add_svar env x t =
    add_var env x G.empty t

  let to_logic_env env = { env with pm = true }
  let to_program_env env = { env with pm = false }
  let is_logic_env env = env.pm

  let lookup env v = Name.M.find v env.vars

  let has_binding env v = Name.M.mem v env.vars

end

let mk_var_with_m_scheme is_constr fix v s =
  { var = v; scheme = s; is_constr = is_constr ; fix = fix }

type error =
  | Basic of string
  | WrongRegionCap
  | WrongRegionCapNumber
  | NotAFunction of M.t
  | Instantiation of Name.t
  | WrongNrConstrArgs of Name.t * int * int

exception Error of Loc.loc * error

let errorm loc s =
  Myformat.ksprintf (fun s -> raise (Error (loc,Basic s))) s

let explain e =
  match e with
  | Basic s -> s
  | WrongRegionCap -> "region capacity is not the one expected here"
  | WrongRegionCapNumber ->
      "the number of region capacities is not the one expected here"
  | Instantiation v ->
      Myformat.sprintf "instantiation of %a: not the right number of arguments"
        Name.print v
  | NotAFunction t ->
      Myformat.sprintf "term is expected to be a function but is of type %a"
        M.print t
  | WrongNrConstrArgs (v,l1,l2) ->
      Myformat.sprintf "constructor %a expects %d arguments, but is given %d"
        Name.print v l1 l2

let error l e = raise (Error (l,e))

let unify t1 t2 loc =
  try U.unify t1 t2
  with U.CannotUnify ->
    errorm loc "Inference: type mismatch between %a and %a"
      M.print t1 M.print t2

exception FindFirst of Name.t

let pref eff cur p =
  I.pure_lam cur (Some (M.map eff)) p p.I.loc

let postf e t old cur res p =
  let l = p.I.loc in
  let lameff s body = I.pure_lam s (Some (M.map e)) body l in
  lameff old (lameff cur (I.pure_lam res t p l))

let type_of_branch (_,_,e) = e.t
let rw_of_branch (_,_,e) = e.e

module Uf = Unionfind

let varfun env v inst l =
(*   Myformat.printf "treating var: %a@." Name.print v.I.var; *)
  let m ,xt =
    try Env.lookup env v.I.var
    with Not_found ->
      errorm l "variable %a not found" Name.print v.I.var in
  let xt = if Env.is_logic_env env then M.to_logic_type xt else xt in
  let nt,i =
    try M.refresh m inst xt
    with Invalid_argument _ -> error l (Instantiation v.I.var) in
  let v = mk_var_with_m_scheme v.I.is_constr v.I.fix v.I.var (m,xt) in
  v, i, nt

let rec check_type env t (x : I.t) =
  let e = infer env x in
  begin try U.unify t e.t
  with U.CannotUnify ->
    errorm e.loc "type error: term has type %a but expected type %a@."
      M.print e.t M.print t
  end ;
  e
and infer env (x : I.t) =
  let l = x.I.loc in
  let e,t,eff =
    match x.I.v with
    | I.Restrict (m,e) ->
        let map' = infer env m in
        begin match Uf.desc map'.t with
          | M.Map em ->
              let em = M.to_effect em in
              let v = PL.var PI.restrict_id in
              let v = I.mkvar false `Prefix v in
              let new_e =
                I.app (I.var ~inst:([],[],[Effect.diff em e; e]) v l) m l in
              let e = infer env new_e in
              e.v, e.t, e.e
          | _ -> assert false
        end
    (* special case for !! *)
    | I.Get (ref, map) ->
        let map' = infer env map in
        let ref' = infer env ref in
        begin match Uf.desc map'.t, Uf.desc ref'.t with
        | M.Map e, M.Ref (r,_) ->
            let e = M.rremove e [r] in
            let e = M.to_effect e in
            let v = PL.var PI.get_id in
            let v = I.mkvar false `Prefix v in
            let new_e =
              I.app (I.app (I.var ~inst:([],[],[e]) v l) ref l) map l in
            let e = infer env new_e in
            e.v, e.t, e.e
        | _, M.Ref _  ->
            errorm l "using !! on term which is not a map but of type
            %a@." M.print map'.t
        | _, _ ->
            errorm l "using !! on term which is not a reference but of type
            %a@." M.print ref'.t
        end
    | I.App (e1,e2) ->
        let e1 = infer env e1 in
        let t1,t2, eff =
          match Uf.desc e1.t with
          | M.Arrow (t1,t2, eff) -> t1,t2, eff
          | M.PureArr (t1,t2) -> t1, t2, M.rw_empty
          | _ -> error l (NotAFunction e1.t)
        in
        let e2 = check_type env t1 e2 in
        App (e1,e2), t2, M.rw_union3 e1.e e2.e eff
    | I.Annot (e,t,rw) ->
        let t' = M.from_ty t in
        let e = check_type env t' e in
        begin match rw with
        | None -> e.v, e.t, e.e
        | Some rw -> Annot (e,t,rw), t', M.from_rw rw
        end
    | I.Const c -> Const c, M.const (Const.type_of_constant c), M.rw_empty
    | I.PureFun (x,nt,e) ->
        let nt = Opt.get_lazy M.new_ty nt in
        let env = Env.add_svar env x nt in
        let e = infer env e in
        PureFun (x,nt, e), M.parr nt e.t, M.rw_empty
    | I.Quant (k,x, nt,e) ->
        let nt = Opt.get_lazy M.new_ty nt in
        let env = Env.add_svar env x nt in
        let e = check_type env M.prop e in
        Quant (k, x, nt, e), M.prop, M.rw_empty
    | I.LetReg (rl,e) ->
        let e = infer env e in
        let eff = M.rw_rremove e.e (List.map M.from_region rl) in
        LetReg (rl,e), e.t, eff
    | I.Ite (e1,e2,e3) ->
        let e1 = check_type env (M.bool ()) e1 in
        let e2 = infer env e2 in
        let e3 = check_type env e2.t e3 in
        Ite (e1,e2,e3), e2.t, M.rw_union3 e1.e e2.e e3.e
    | I.Gen (g,e) ->
        let e = infer env e in
        Gen (g,e), e.t, e.e
    | I.Param (t,eff) ->
        let rw = M.from_rw eff in
        Param (t,eff), M.from_ty t, rw
    | I.For (dir,inv,i,s,e,body) ->
        let env = Env.add_svar env i M.int in
        let body = check_type env (M.unit ()) body in
        let inv = pre env (fst body.e) inv l in
        For (dir, inv, i, s, e, body), (M.unit ()), body.e
    | I.HoareTriple (p,e,q) ->
        let e = infer (Env.to_program_env env) e in
        let p = pre env (fst e.e) p l in
        let q = post env e.e e.t q l in
        HoareTriple (p,e,q), M.prop, M.rw_empty
    | I.Var (v,inst) ->
        let v, i, nt = varfun env v inst l in
        Var (v, i), nt, M.rw_empty
    | I.Case (e,bl) ->
        let e = infer env e in
        let bl = List.map (branch env e.t) bl in
        ExtList.two_iter (fun a b ->
          unify (type_of_branch a) (type_of_branch b) l) bl;
        let rt =
          let _,_,e = List.hd bl in
          e.t in
        let rw = List.fold_left (fun acc b ->
          M.rw_union acc (rw_of_branch b)) e.e bl in
        Case (e,bl), rt, rw
    | I.Let (g,e1,x,e2,r) ->
        let env, e1 = letgen env x g e1 r in
        let e2 = infer env e2 in
        Let (g, e1,x,e2, r), e2.t, M.rw_union e1.e e2.e
    | I.Lam (x,xt,(p,e,q)) ->
        let nt = M.from_ty xt in
        let env = Env.add_svar env x nt in
        let e = infer (Env.to_program_env env) e in
        let p = pre env (fst e.e) p l in
        let q = post env e.e e.t q l in
        Lam (x,xt,(p,e,q)), M.arrow nt e.t e.e, M.rw_empty
  in
  { v = e ; t = t ; e  = eff ; loc = l }
and pre env eff (cur,x) l =
  let p =
    match x with
    | Some ({ I.v = I.PureFun _} as f) -> f
    | _ ->
        let f = match x with
        | None -> I.ptrue l
        | Some f -> f in
        pref eff cur f in
  check_type (Env.to_logic_env env) (M.base_pre_ty eff) p

and post env eff t (old,cur,x) l =
  let t = M.to_logic_type t in
  let eff = M.overapprox eff in
  let bp = M.base_post_ty eff t in
  let p =
    match x with
    | I.PPlain ({ I.v = I.PureFun _ } as f) -> f
    | _ ->
        let r, f =
          match x with
          | I.PNone -> Name.new_anon (), I.ptrue l
          | I.PPlain f -> Name.new_anon (), f
          | I.PResult (r,f) -> r, f in
        postf eff (Some t) old cur r f in
  check_type (Env.to_logic_env env) bp p

and branch env exp (nvl, p, e) =
  let env, p = pattern env exp p in
  nvl, p, infer env e

and pattern_node env exp p l =
  match p with
  | I.PVar v ->
      assert (not (Env.has_binding env v));
      Env.add_svar env v exp, PVar v, exp
  | I.PApp (v,pl) ->
      let v, i, nt = varfun env v ([],[],[]) l in
      assert (v.is_constr);
      let tl, rt = M.nsplit nt in
      U.unify exp rt;
      let env, pl =
        try
          List.fold_left2 (fun (env, pl) t p ->
            let env, p = pattern env t p in
            env, p::pl) (env,[]) tl pl
        with Invalid_argument "List.fold_left2" ->
          error l (WrongNrConstrArgs (v.var, List.length tl, List.length pl))
          in
      env, PApp (v, i, List.rev pl), rt
and pattern env exp p =
  let l = p.I.ploc in
  let env, p', t = pattern_node env exp p.I.pv l in
  env, { pv = p' ; pt = t; ploc = l  }

and letgen env x g e r =
  let env' =
    match r with
    | Const.NoRec -> env
    | Const.Rec ty -> Env.add_svar env x (M.from_ty ty) in
  let e = infer env' e in
  Env.add_var env x g e.t, e

let rec infer_th env d =
  match d with
  | I.Formula (s,e,k) -> env, Formula (s,check_type env M.prop e, k)
  | I.Section (s,cl,th) ->
      let env, dl = theory env th in
      env, Section (s,cl,dl)
  | I.Logic (n,g,t, f) ->
      let env = Env.add_var env n g (M.from_ty t) in
(*       Myformat.printf "added: %a : %a@." Name.print n Ty.print t; *)
      env, Logic (n,g,t, f)
  | I.TypeDef (n,tl,k) ->
      let env = typedef env tl n k in
      env, TypeDef (n,tl, k)
  | I.DLetReg rl -> env, DLetReg rl
  | I.DGen g -> env, DGen g
  | I.Program (x,g,e,r,fix) ->
      let env,e = letgen env x g e r in
      env, Program (x,g,e,r,fix)
  | I.Fixpoint (x,g,ty,e,fix) ->
      let env, e = letgen env x g e (Const.Rec ty) in
      env, Fixpoint (x,g,ty,e,fix)
  | I.Inductive (n,g,t,tel) ->
      let inner_env = Env.add_svar env n (M.from_ty t) in
      let tel = List.map (fun (n,t) -> n,check_type inner_env M.prop t) tel in
      let env = Env.add_var env n g (M.from_ty t) in
      env, Inductive (n,g,t,tel)
and theory env th = ExtList.fold_map infer_th env th
and typedef env tl n k =
  match k with
  | Ast.Abstract -> env
  | Ast.ADT bl ->
      let base = Ty.app n (List.map Ty.var tl) in
      List.fold_left (cbranch tl base) env bl
and cbranch tvl base env (n,tl) =
  let t = Ty.nparr tl base in
  Env.add_var env n (tvl,[],[]) (M.from_ty t)
let theory th =
  let _, th = theory Env.empty th in
  th
