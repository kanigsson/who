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

module SM = Misc.StringMap
module G = Ty.Generalize
module NM = Name.M
module IT = ParseTypes

type error =
  | UnknownVar of string * string
  | EffectOrRegionArgumentsToAbstractType

exception Error of error

let explain e =
  match e with
  | UnknownVar (s,x) ->
      Myformat.sprintf "unknown %s var: %s" s x
  | EffectOrRegionArgumentsToAbstractType ->
      "Region or effect arguments are not allowed for abstract types."

let error kind = raise (Error kind)

module Env : sig
  type t
  (* the environment maps each variable name to a
     unique name *)
  val empty : t

  val var : t -> string -> Name.t
  val rvar : t -> string -> Name.t
  val effvar : t -> string -> Name.t
  val tyvar : t -> string -> Name.t

  val typedef : t -> string -> Ty.Generalize.t * Ty.t

  val add_var : t -> ?ty:(Ty.Generalize.t * Ty.t) -> string -> t * Name.t
  val add_ex_var : t -> ?ty:(Ty.Generalize.t * Ty.t) -> string -> Name.t -> t
  val add_rvars : t -> string list -> t * Name.t list
  val add_tvars : t -> string list -> t * Name.t list
  val add_global_tyvar : t -> string -> t * Name.t
  val add_type_def : t -> string -> Ty.Generalize.t -> Ty.t -> t
  val add_gen : t -> ParseTree.generalize -> t * Ty.Generalize.t

  val only_add_type : t -> Name.t -> Ty.Generalize.t * Ty.t -> t
  val lookup_type : t -> Name.t -> Ty.Generalize.t * Ty.t

end = struct

  type t =
    {
      v : Name.t SM.t ;
      t : Name.t SM.t ;
      r : Name.t SM.t ;
      e : Name.t SM.t ;
      tyrepl : (Ty.Generalize.t * Ty.t) Misc.StringMap.t ;
      typing : (Ty.Generalize.t * Ty.t) NM.t
    }

  let empty =
    { v = SM.empty; t = SM.empty;
      r = SM.empty; e = SM.empty;
      tyrepl = Misc.StringMap.empty;
      typing = NM.empty ;
    }

  let gen_var s m x =
    try SM.find x m with Not_found -> error (UnknownVar (s,x))

  let var env = gen_var "program" env.v
  let tyvar env = gen_var "type" env.t
  let rvar env = gen_var "region" env.r
  let effvar env = gen_var "effect" env.e

  let only_add_type env x g =
    { env with typing = NM.add x g env.typing }

  let add_ex_var env ?ty x y =
    let env = match ty with
    | None -> env
    | Some t -> only_add_type env y t in
    { env with v = SM.add x y env.v }

  let add_var env ?ty x =
    let y = Name.from_string x in
    add_ex_var env ?ty x y, y

  let add_tvar env x =
    let y = Name.from_string x in
    { env with t = SM.add x y env.t; }, y

  let add_rvars env l =
    let r, nl =
      List.fold_left
        (fun (r,l) x ->
          let nv = Name.from_string x in
          SM.add x nv r, nv::l) (env.r,[]) l in
    { env with r = r }, nl

  let add_tvars env l =
    List.fold_left (fun (acc,l) x ->
      let env, nv = add_tvar acc x in
      env, nv::l) (env,[]) l

  let add_global_tyvar env s =
    let env, n = add_tvar env s in
    Predefty.add_symbol s n;
    env, n

  let add_type_def env n g t =
    { env with tyrepl = Misc.StringMap.add n (g,t) env.tyrepl }

  let add_evars env l =
    let e, nl =
      List.fold_left
        (fun (e,l) x ->
          let nv = Name.from_string x in
          SM.add x nv e, nv::l) (env.e,[]) l in
    { env with e = e }, nl

  let add_gen env (tl,rl,el) =
    let env, tl = add_tvars env tl in
    let env, rl = add_rvars env rl in
    let env, el = add_evars env el in
    env, (List.rev tl,List.rev rl,List.rev el)

  let typedef env x = Misc.StringMap.find x env.tyrepl

  let lookup_type env x =
    NM.find x env.typing

  let annot env m = { env with typing = m }

end


let effect env (rl,el) =
  Effect.from_lists
    (List.map (Env.rvar env) rl)
    (List.map (Env.effvar env) el)

let ty env t =
  let rec aux = function
    | IT.TVar v -> Ty.var (Env.tyvar env v)
    | IT.TConst c -> Ty.const c
    | IT.Tuple tl -> Ty.tuple (List.map aux tl)
    | IT.Arrow (t1,t2,e,cap) ->
        Ty.caparrow (aux t1) (aux t2) (effect env e)
          (List.map (Env.rvar env) cap)
    | IT.PureArr (t1,t2) -> Ty.parr (aux t1) (aux t2)
    | IT.TApp (v,i) ->
        let i = inst i in
        begin try
          let g,t = Env.typedef env v in
          Ty.allsubst g i t
        with Not_found ->
          let v = Env.tyvar env v in
          let tl,rl,el = i in
          if rl = [] && el = [] then Ty.app v tl
          else error EffectOrRegionArgumentsToAbstractType
        end
    | IT.Ref (r,t) -> Ty.ref_ (Env.rvar env r) (aux t)
    | IT.Map e -> Ty.map (effect env e)
    | IT.ToLogic t -> Ty.to_logic_type (aux t)
  and inst i = Inst.map aux (Env.rvar env) (effect env) i in
  aux t

let rec_ env = function
  | Const.Rec t -> Const.Rec (ty env t)
  | Const.NoRec -> Const.NoRec
  | Const.LogicDef -> Const.LogicDef
