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

open Ast
module SM = Misc.StringMap
module G = Ty.Generalize
module U = Unify

module S = Name.S
module AI = Ast.Infer
module PL = Predefined.Logic

module Env : sig
  type t

  val empty : t

  val add_var : t -> Name.t -> G.t -> Ty.t -> t
  val add_svar : t -> Name.t -> Ty.t -> t

  val lookup : t -> Name.t -> G.t * Ty.t

  val add_ty : t -> Name.t -> G.t -> Ty.t option -> t

  val to_logic_env : t -> t
  val to_program_env : t -> t
  val is_logic_env : t -> bool

end = struct
  type t = {
    vars : (G.t * Ty.t) Name.M.t ;
    types : (G.t * Ty.t option) Name.M.t;
    pm : bool;
    }

  let empty = { vars = Name.M.empty; pm = false; types = Name.M.empty; }
  let add_var env x g t =
    { env with vars = Name.M.add x (g,t) env.vars }
  let add_svar env x t =
    add_var env x G.empty t
  let add_ty env x g t =
    { env with types = Name.M.add x (g,t) env.types }

  let to_logic_env env = { env with pm = true }
  let to_program_env env = { env with pm = false }
  let is_logic_env env = env.pm

  let lookup env v = Name.M.find v env.vars

end

exception Error of string * Loc.loc

let error loc s =
  Myformat.ksprintf (fun s -> raise (Error (s,loc))) s

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

exception FindFirst of Name.t

let to_uf_node (tl,rl,evl) el (x : Ty.t ) =
  let x = Ty.elsubst evl el x in
  let tn,th = bh U.new_ty tl and rn,rh = bh U.new_r rl in
  let rec aux' f x =
    match x with
    | (Ty.Const c) -> Unify.const c
    | Ty.Arrow (t1,t2,e, c) ->
        U.arrow (f t1) (f t2) (eff e) (List.map auxr c)
    | Ty.Tuple tl -> U.tuple (List.map f tl)
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
      when PI.unsafe_equal v PI.get_id ->
        let map' = infer env map in
        let ref' = infer env ref in
        begin match Uf.desc map'.t, Uf.desc ref'.t with
        | U.T Ty.Map e, U.T Ty.Ref (r,_) ->
            let e = U.rremove e [r] in
            let e = U.to_eff e in
            let new_e = AP.app (AP.app (AP.var ~inst:[e] v l) ref l) map l in
            let e = infer env new_e in
            e.v, e.t, e.e
        | _, U.T Ty.Ref _  ->
            error l "using !! on term %a which is not a map but of type
            %a@." AP.print map U.print_node map'.t
        | _, _ ->
            error l "using !! on term %a which is not a reference but of type
            %a@." AP.print ref U.print_node ref'.t
        end
    (* special case for restrict *)
    | App ({ v = Var (v,([],[],[e]))},m,`Prefix,[])
        when PI.unsafe_equal v PI.restrict_id ->
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
        let env = Env.add_svar env x xt in
        let e = infer env e in
        PureFun (xt, Name.close_bind x e), U.parr nt e.t, U.eff_empty
    | Quant (k,xt,(_,x,e)) ->
        let env = Env.add_svar env x xt in
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
        let env = Env.add_svar env i Ty.int in
        let body = check_type env U.unit body in
        let inv = pre env body.e inv l in
        For (dir, inv, i, s, e, body), U.unit, body.e
    | HoareTriple (p,e,q) ->
        let e = infer (Env.to_program_env env) e in
        let p = pre env e.e p l in
        let q = post env e.e e.t q l in
        HoareTriple (p,e,q), U.prop, U.eff_empty
    | Var (v,(_,_,el)) ->
(*         Myformat.printf "treating var: %a@." Name.print v; *)
        let (_,_,evl) as m ,xt =
          try Env.lookup env v
          with Not_found -> error l "variable %a not found" Name.print v in
        let xt = if Env.is_logic_env env then Ty.to_logic_type xt else xt in
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
    | Lam (x,xt,cap,(p,e,q)) ->
        let nt = sto_uf_node xt in
        let env = Env.add_svar env x xt in
        let e = infer (Env.to_program_env env) e in
        let p = pre env e.e p l in
        let q = post env e.e e.t q l in
        Lam (x,xt,cap,(p,e,q)), U.arrow nt e.t e.e (List.map to_uf_rnode cap),
        U.eff_empty
  in
  { v = e ; t = t ; e  = eff ; loc = l }
and pre env eff (cur,x) l : AI.pre' =
  let f = match x with
  | None -> ParseT.ptrue l
  | Some f -> f in
  let res =
    check_type (Env.to_logic_env env) (U.base_pre_ty eff) (pref eff cur f) in
  cur, Some res

and post env eff t (old,cur,x) l =
  let t = U.to_logic_type t in
  let bp = U.base_post_ty eff t in
  let r, f =
    match x with
    | PNone -> Name.new_anon (), ParseT.ptrue l
    | PPlain f -> Name.new_anon (), f
    | PResult (r,f) -> r, f in
  let p = postf eff t old cur r f in
  let res = check_type (Env.to_logic_env env) bp p in
  old, cur, PPlain res

and letgen env x g e r =
  let env' =
    match r with
    | Const.NoRec | Const.LogicDef -> env
    | Const.Rec ty -> Env.add_svar env x ty in
  let e = infer env' e in
  let xt =
    try U.to_ty e.t
    with Assert_failure _ ->
      error e.loc "could not determine the type of: %a : %a@." Name.print x
        U.print_node e.t in
  Env.add_var env x g xt, e

let rec infer_th env d =
  match d with
  | Formula (s,e,k) -> env, Formula (s,check_type env U.prop e, k)
  | Section (s,cl,th) ->
      let env, dl = theory env th in
      env, Section (s,cl,dl)
  | Logic (n,g,t) ->
      let env = Env.add_var env n g t in
(*       Myformat.printf "added: %a : %a@." Name.print n Ty.print t; *)
      env, Logic (n,g,t)
  | TypeDef (g,t,n) ->
      let env = Env.add_ty env n g t in
      env, TypeDef (g,t,n)
  | DLetReg rl -> env, DLetReg rl
  | DGen g -> env, DGen g
  | Program (x,g,e,r) ->
      let env,e = letgen env x g e r in
      env, Program (x,g,e,r)
and theory env th = Misc.list_fold_map infer_th env th

let prelude_env, prelude =
  theory Env.empty Internalize.prelude

let theory th =
  let _, th = theory prelude_env th in
  th
