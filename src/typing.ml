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
open Ty
module SM = Misc.StringMap
module SS = Misc.StringSet
module RS = Name.S

module G = Generalize

type error =
  | NonDisjointEffects
  | KindAnnotationMismatch of Name.t * Ty.scheme * Ty.scheme
  | TyAnnotationMismatch of Ast.t * Ty.t * Ty.t
  | EffectinLogic
  | Unboundvar of Name.t
  | NotAFunction of Ty.t
  | TyAppmismatch of Ty.t * Ty.t
  | TyMismatch of Ty.t * Ty.t
  | CapMismatch of Name.t list * Name.t list
  | PatternArgs of Name.t
  | Other of string

exception Error of Loc.loc * error

let explain e =
  match e with
  | NonDisjointEffects -> "double effect"
  | KindAnnotationMismatch (x,s1,s2) ->
      Myformat.sprintf
        "internal error:
         annotation mismatch on var %a: annotation: %a but in environment: %a"
        Name.print x Ty.print_scheme s1 Ty.print_scheme s2 ;
  | Unboundvar v ->
      Myformat.sprintf "unknown variable: %a" Name.print v
  | EffectinLogic -> "effectful application not allowed in logic"
  | NotAFunction t ->
      Myformat.sprintf "expected a function, but is of type %a" Ty.print t
  | TyMismatch (t1,t2) ->
      Myformat.sprintf "expected object of type %a, but it has type %a"
        Ty.print t1 Ty.print t2
  | TyAppmismatch (t1,t2) ->
      Myformat.sprintf "expected argument of type %a, but is of type %a"
        Ty.print t1 Ty.print t2
  | TyAnnotationMismatch (e,t1,t2) ->
      Myformat.sprintf
        "expression %a is annotated with type %a, but has type %a"
        Ast.print e Ty.print t1 Ty.print t2
  | CapMismatch (c1,c2) ->
      Myformat.sprintf
        "mismatch on creation permissions: expected %a, given %a"
        Name.print_list c1 Name.print_list c2
  | PatternArgs n ->
      Myformat.sprintf
        "constructor %a has not been given the right number of arguments"
        Name.print n
  | Other s -> s

let error loc e = raise (Error (loc, e))

let errorm loc s =
  Myformat.ksprintf (fun s -> raise (Error (loc, Other s))) s

(* TODO build environment module *)
module Env : sig
  type t
  val empty : t
  val add_var : t -> Name.t -> G.t -> Ty.t -> t
  val add_svar : t -> Name.t -> Ty.t -> t
  val has_binding : t -> Name.t -> bool
  val lookup : t -> Name.t -> G.t * Ty.t
  val print_domain : t Myformat.fmt
end = struct
  type t = (G.t * Ty.t) Name.M.t

  let empty = Name.M.empty
  let add_var env x g t = Name.M.add x (g,t) env
  let add_svar env x t = Name.M.add x (G.empty,t) env

  let has_binding env x = Name.M.mem x env

  let lookup env x = Name.M.find x env

  let print_domain fmt env =
    Name.M.iter (fun x _ -> Myformat.fprintf fmt "%a;" Name.print x) env
end

let disjoint_union loc s1 s2 =
  if RS.is_empty (RS.inter s1 s2) then RS.union s1 s2
  else error loc NonDisjointEffects

let disj_union3 loc s1 s2 s3 =
  disjoint_union loc (disjoint_union loc s1 s2) s3


let type_of_var loc env x =
  let g = Env.lookup env x.var in
  if not (Ty.scheme_equal x.scheme g) then
  if not (Ty.scheme_equal x.scheme g) then
    error loc (KindAnnotationMismatch (x.var,x.scheme, g));
  g

let ftype_of_var loc env x =
  let m,t = Env.lookup env x.var in
  let g = m, to_logic_type t in
  if not (Ty.scheme_equal x.scheme g) then
    error loc (KindAnnotationMismatch (x.var,x.scheme, g));
  g

let prety = Ty.base_pretype
let postty eff t = Ty.base_posttype (Ty.to_logic_type t) eff

let set_list_contained l s =
  RS.for_all (fun x -> List.exists (fun y -> Name.equal x y) l) s

(* TODO hybrid environment *)
let rec formtyping' env loc = function
  | Ast.Const c -> Ty.const (Const.type_of_constant c)
  | Ast.Var (s,i) ->
      begin try
        let g, t = ftype_of_var loc env s in
        let r = Ty.allsubst g i t in
(*         printf "var : %a of type %a@." Vars.var s Ty.print r; r *)
        r
      with Not_found -> error loc (Unboundvar s.var)
      end
  | Ast.App (e1,e2) ->
      let t1 = formtyping env e1 in
      let t2 = formtyping env e2 in
(*
      Myformat.printf "app of %a and %a of types %a and %a@."
      Recon.print e1 Recon.print e2 Ty.print t1 Ty.print t2;
*)
      begin match t1 with
      | Arrow _ -> error loc EffectinLogic
      | PureArr (ta,tb) ->
          if Ty.equal ta t2 then tb else error loc (TyAppmismatch (ta, t2))
      | t -> error loc (NotAFunction t)
      end
  | PureFun (t,b) ->
      let x,e = vopen b in
      parr t (formtyping (Env.add_svar env x t) e)
  | Quant (_,t,b) ->
      let x,e = vopen b in
      fis_oftype (Env.add_svar env x t) prop e;
      prop
  | Ite (e1,e2,e3) ->
      fis_oftype env (bool ()) e1;
      let t = formtyping env e2 in
      fis_oftype env t e3;
      t
  | Lam (x,t,(p,e,q)) ->
      let env = Env.add_svar env x t in
      let t',eff = typing env e in
      pre env eff p;
      post env eff t' q;
      to_logic_type (arrow t t' eff)
  | Gen (_,e)-> formtyping env e
  | Let (g,e1,b,_) ->
      Myformat.printf "formlet@.";
      let x,e2 = vopen b in
(*       Myformat.printf "let: %a@." Name.print x; *)
      let t = formtyping env e1 in
      let env = Env.add_var env x g t in
      let t = formtyping env e2 in
      t
  | HoareTriple (p,e,q) ->
      let t', eff = typing env e in
      pre env eff p;
      post env eff t' q;
      prop
  | Case (t,bl) ->
      let t = formtyping env t in
      let tl = List.map (formbranch env t) bl in
      begin match tl with
      | [] -> assert false
      | t::tl ->
          assert (List.for_all (Ty.equal t) tl);
          t
      end
  | Param _ -> errorm loc "effectful parameter in logic"
  | LetReg _ -> assert false
and formtyping env (e : Ast.t) : Ty.t =
(*   Myformat.printf "formtyping %a@." Ast.print e; *)
  let t = formtyping' env e.loc e.v in
  if Ty.equal e.t t then
    if Rw.is_empty e.e then t
    else errorm e.loc "not empty: %a" Rw.print e.e
  else error e.loc (TyAnnotationMismatch (e, e.t, t))

and pre env eff f = fis_oftype env (prety (Rw.overapprox eff)) f
and post env eff t f = fis_oftype env (postty (Rw.overapprox eff) t) f

and formbranch env exp_pat b =
  let _, p, t = popen b in
  let env = pattern env exp_pat p in
  formtyping env t

and branch env exp_pat b =
  let _, p, t = popen b in
  let env = pattern env exp_pat p in
  typing env t

and pattern env exp p =
  let loc = p.ploc in
  match p.pv with
  | PVar v ->
      assert (not (Env.has_binding env v));
      Env.add_svar env v exp
  | PApp (v,i,pl) ->
    begin try
      assert (v.is_constr);
      let g,t = ftype_of_var loc env v in
      let t = Ty.allsubst g i t in
      let tl,rt = Ty.nsplit t in
      assert (Ty.equal rt exp);
      let env = List.fold_left2 pattern env tl pl in
      env
    with
    | Not_found -> error loc (Unboundvar v.var)
    | Invalid_argument "List.fold_left2" ->
        error loc (PatternArgs v.var)
    end




and typing' env loc = function
  | Ast.Const c ->
      Ty.const (Const.type_of_constant c), Rw.empty
  |Ast.Var (s,i) ->
      begin try
        let g, t = type_of_var loc env s in
        Ty.allsubst g i t, Rw.empty
      with Not_found -> error loc (Unboundvar s.var) end
  | Ast.App (e1,e2) ->
      let t1, eff1 = typing env e1 in
      let t2,eff2 = typing env e2 in
      let effi = Rw.union eff2 eff1 in
(*
      printf "app of %a and %a: eff1:%a eff2:%a@."
      Recon.print e1 Recon.print e2 Effect.print eff1 Effect.print eff2;
*)
      begin match t1 with
      | Arrow (ta,tb,eff) ->
          if Ty.equal ta t2 then tb, Rw.union eff effi
          else error loc (TyAppmismatch (ta,t2))
      | PureArr (ta,tb) ->
          if Ty.equal ta t2 then tb, effi
          else error loc (TyAppmismatch (ta,t2))
      | _ -> error loc (NotAFunction t1)
      end
  | Lam (x,t,(p,e,q)) ->
      let env = Env.add_svar env x t in
      let t',eff = typing env e in
      pre env eff p;
      post env eff t' q;
      arrow t t' eff, Rw.empty
  | Let (g,e1,b,r) ->
      let x, e2 = vopen b in
      let env, eff1 = letgen env x g e1 r in
      let t, eff2 = typing env e2 in
      t, Rw.union eff1 eff2
  | Param (t,e) -> t,e
  | PureFun (t,b) ->
      let x,e = vopen b in
      let env = Env.add_svar env x t in
      let t', eff = typing env e in
      if Rw.is_empty eff then parr t t', eff
      else errorm loc "effectful pure function"
  | Quant (_,t,b) ->
      let x, e = vopen b in
      let env = Env.add_svar env x t in
      let t', eff = typing env e in
      if Rw.is_empty eff && Ty.equal t' Ty.prop then Ty.prop, eff
      else error loc (TyMismatch (Ty.prop, t'))
  | Ite (e1,e2,e3) ->
      let t1, eff1 = typing env e1 in
      if Ty.equal t1 (Ty.bool ()) then
        let t2, eff2 = typing env e2 in
        let t3, eff3 = typing env e3 in
        if Ty.equal t2 t3 then t2, Rw.union3 eff1 eff2 eff3
        else error e3.loc (TyMismatch (t2, t3))
      else error e1.loc (TyMismatch (Ty.bool (), t1))
  | LetReg (vl,e) ->
      let t, eff = typing env e in
      t, Rw.rremove eff vl
  | Case (e,bl) ->
      let t,eff = typing env e in
      let tl, effl = List.split (List.map (branch env t) bl) in
      begin match tl with
      | [] -> assert false
      | t::tl ->
          assert (List.for_all (Ty.equal t) tl);
          t, List.fold_left Rw.union eff effl
      end
  | Gen _ -> assert false
  | HoareTriple (p,e,q) ->
      let t', eff = typing env e in
      pre env eff p;
      post env eff t' q;
      prop, Rw.empty

and typing env (e : Ast.t) : Ty.t * Rw.t =
(*   Myformat.printf "typing %a@." Ast.print e; *)
  let ((t',_) as x) = typing' env e.loc e.v in
  if Ty.equal e.t t' then x else error e.loc (TyAnnotationMismatch (e,e.t,t'))
and fis_oftype env t e =
  let t' = formtyping env e in
  if Ty.equal t t' then () else error e.loc (TyMismatch (t,t'))

and letgen env x g e r =
  if not ( G.is_empty g || is_value e) then
        errorm e.loc "generalization over non-value";
  let env' =
    match r with
    | Const.NoRec | Const.LogicDef -> env
    | Const.Rec t -> Env.add_svar env x t in
  let t, eff =
    if r = Const.LogicDef then formtyping env' e, Rw.empty
    else typing env' e in
  let env = Env.add_var env x g t in
  env, eff

let rec decl env d =
  match d with
  | Formula (_,f,_) -> fis_oftype env prop f; env
  | Section (_,th,_) -> theory env th
  | DLetReg _ | DGen _ | Decl _ -> env
  | Logic (n,(g,t)) -> Env.add_var env n g t
  | Inductive (n,g,t,tel) ->
      let env = Env.add_var env n g t in
      List.iter (fis_oftype env prop) tel;
      env
  | TypeDef (_, _, Abstract) -> env
  | TypeDef (n, tvl, ADT bl) ->
      let bt = Ty.app n (List.map Ty.var tvl) in
      List.fold_left (fun env (n,tl) ->
        let t = Ty.nparr tl bt in
        Env.add_var env n (tvl,[],[]) t) env bl
  | Program (x,g,e,r) ->
      let env,  _ = letgen env x g e r in
      env

and theory env th = List.fold_left decl env th

let typing t = ignore (typing Env.empty t)
let formtyping t = ignore (formtyping Env.empty t)
let theory th = ignore (theory Env.empty th)
