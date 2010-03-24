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
module PI = Predefined.Identifier
module M = MutableType
module SM = Misc.StringMap
module G = Ty.Generalize
module U = Unify

module S = Name.S
module PL = Predefined.Logic

module Env : sig
  type t

  val empty : t

  val add_var : t -> Name.t -> G.t -> M.t -> t
  val add_svar : t -> Name.t -> M.t -> t

  val lookup : t -> Name.t -> G.t * M.t

  val to_logic_env : t -> t
  val to_program_env : t -> t
  val is_logic_env : t -> bool

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

end

exception Error of string * Loc.loc

let error loc s =
  Myformat.ksprintf (fun s -> raise (Error (s,loc))) s

let unify t1 t2 loc =
  try U.unify t1 t2
  with U.CannotUnify ->
    (* FIXME *) assert false
(*
    error loc "Inference: type mismatch between %a and %a"
      U.print_node t1 U.print_node t2
*)

exception FindFirst of Name.t

let pref eff cur p =
  I.pure_lam cur (M.map eff) p p.I.loc

let postf eff t old cur res p =
  let l = p.I.loc in
  let lameff s body = I.pure_lam s (M.map eff) body l in
  lameff old (lameff cur (I.pure_lam res t p l))

module Uf = Unionfind

let rec check_type env t (x : I.t) =
  let e = infer env x in
  begin try U.unify t e.t
  with U.CannotUnify ->
    (* FIXME *) assert false
(*
    error e.loc "type error: term has type %a but expected type %a@."
      U.print_node e.t U.print_node t
*)
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
              let new_e =
                I.app (I.var ~inst:[Effect.diff em e; e] v l) m l in
              let e = infer env new_e in
              e.v, e.t, e.e
          | _ -> assert false
        end
    (* special case for !! *)
    (** TODO special construct in this case *)
    | I.App ({ I.v = I.App ({ I.v = I.Var (v,[]) }, ref,`Prefix,[]) },
      map, `Prefix, [])
      when PI.unsafe_equal v PI.get_id ->
        let map' = infer env map in
        let ref' = infer env ref in
        begin match Uf.desc map'.t, Uf.desc ref'.t with
        | M.Map e, M.Ref (r,_) ->
            let e = M.rremove e [r] in
            let e = M.to_effect e in
            let new_e = I.app (I.app (I.var ~inst:[e] v l) ref l) map l in
            let e = infer env new_e in
            e.v, e.t, e.e
        | _, M.Ref _  ->
           (* FIXME *) assert false
(*
            error l "using !! on term %a which is not a map but of type
            %a@." I.print map U.print_node map'.t
*)
        | _, _ ->
           (* FIXME *) assert false
(*
            error l "using !! on term %a which is not a reference but of type
            %a@." I.print ref U.print_node ref'.t
*)
        end
    | I.App (e1,e2, k, cap) ->
        let e1 = infer env e1 in
        let t1,t2, eff =
          match Uf.desc e1.t with
          | M.Arrow (t1,t2, eff, cap') ->
              List.iter2 (fun a b -> U.runify a (M.from_region b)) cap' cap;
              t1,t2, eff
          | M.PureArr (t1,t2) -> t1, t2, M.eff_empty
          | _ ->
              (* FIXME *) assert false
(*
              error l "term is expected to be a function but is of type %a"
                U.print_node e1.t
*)
        in
        let e2 = check_type env t1 e2 in
        App (e1,e2,k, cap), t2, M.eff_union3 e1.e e2.e eff
    | I.Annot (e,t) ->
        let t' = M.from_ty t in
        let e = check_type env t' e in
        Annot (e,t), t', e.e
    | I.Const c -> Const c, M.const (Const.type_of_constant c), M.eff_empty
    | I.PureFun (nt,(_,x,e)) ->
        let env = Env.add_svar env x nt in
        let e = infer env e in
        PureFun (nt, Name.close_bind x e), M.parr nt e.t, M.eff_empty
    | I.Quant (k,nt,(_,x,e)) ->
        let env = Env.add_svar env x nt in
        let e = check_type env M.prop e in
        Quant (k, nt, Name.close_bind x e), M.prop, M.eff_empty
    | I.LetReg (rl,e) ->
        let e = infer env e in
        let eff = M.rremove e.e (List.map M.from_region rl) in
        LetReg (rl,e), e.t, eff
    | I.Ite (e1,e2,e3) ->
        let e1 = check_type env M.bool e1 in
        let e2 = infer env e2 in
        let e3 = check_type env e2.t e3 in
        Ite (e1,e2,e3), e2.t, M.eff_union3 e1.e e2.e e3.e
    | I.Gen (g,e) ->
        let e = infer env e in
        Gen (g,e), e.t, e.e
    | I.Param (t,eff) ->
        Param (t,eff), M.from_ty t, M.from_effect eff
    | I.For (dir,inv,i,s,e,body) ->
        let env = Env.add_svar env i M.int in
        let body = check_type env M.unit body in
        let inv = pre env body.e inv l in
        For (dir, inv, i, s, e, body), M.unit, body.e
    | I.HoareTriple (p,e,q) ->
        let e = infer (Env.to_program_env env) e in
        let p = pre env e.e p l in
        let q = post env e.e e.t q l in
        HoareTriple (p,e,q), M.prop, M.eff_empty
    | I.Var (v,el) ->
(*         Myformat.printf "treating var: %a@." Name.print v; *)
        let (_,_,evl) as m ,xt =
          try Env.lookup env v
          with Not_found -> error l "variable %a not found" Name.print v in
        let xt = if Env.is_logic_env env then M.to_logic_type xt else xt in
        let nt,i =
          try M.refresh m el xt
          with Invalid_argument "List.fold_left2" ->
            error l "not the right number of effect vars: %a@.\
            I expected %d variables, but you gave %d effects.@."
            Name.print v (List.length evl) (List.length el) in
(*         Myformat.printf "found type: %a@." U.print_node nt; *)
        Var (v, i), nt, M.eff_empty
    | I.Let (g,e1,(_,x,e2),r) ->
        let env, e1 = letgen env x g e1 r in
        let e2 = infer env e2 in
        Let (g, e1,Name.close_bind x e2,r), e2.t, M.eff_union e1.e e2.e
    | I.Lam (x,xt,cap,(p,e,q)) ->
        let nt = M.from_ty xt in
        let env = Env.add_svar env x nt in
        let e = infer (Env.to_program_env env) e in
        let p = pre env e.e p l in
        let q = post env e.e e.t q l in
        Lam (x,xt,cap,(p,e,q)), M.arrow nt e.t e.e (List.map M.from_region cap),
        M.eff_empty
  in
  { v = e ; t = t ; e  = eff ; loc = l }
and pre env eff (cur,x) l =
  let f = match x with
  | None -> I.ptrue l
  | Some f -> f in
  check_type (Env.to_logic_env env) (M.base_pre_ty eff) (pref eff cur f)

and post env eff t (old,cur,x) l =
  let t = M.to_logic_type t in
  let bp = M.base_post_ty eff t in
  let r, f =
    match x with
    | I.PNone -> Name.new_anon (), I.ptrue l
    | I.PPlain f -> Name.new_anon (), f
    | I.PResult (r,f) -> r, f in
  let p = postf eff t old cur r f in
  check_type (Env.to_logic_env env) bp p

and letgen env x g e r =
  let env' =
    match r with
    | Const.NoRec | Const.LogicDef -> env
    | Const.Rec ty -> Env.add_svar env x (M.from_ty ty) in
  let e = infer env' e in
  Env.add_var env x g e.t, e

let rec infer_th env d =
  match d with
  | I.Formula (s,e,k) -> env, Formula (s,check_type env M.prop e, k)
  | I.Section (s,cl,th) ->
      let env, dl = theory env th in
      env, Section (s,cl,dl)
  | I.Logic (n,g,t) ->
      let env = Env.add_var env n g (M.from_ty t) in
(*       Myformat.printf "added: %a : %a@." Name.print n Ty.print t; *)
      env, Logic (n,g,t)
  | I.TypeDef (g,t,n) ->
      env, TypeDef (g,t,n)
  | I.DLetReg rl -> env, DLetReg rl
  | I.DGen g -> env, DGen g
  | I.Program (x,g,e,r) ->
      let env,e = letgen env x g e r in
      env, Program (x,g,e,r)
and theory env th = Misc.list_fold_map infer_th env th

let prelude_env, prelude =
  theory Env.empty Internalize.prelude

let theory th =
  let _, th = theory prelude_env th in
  th
