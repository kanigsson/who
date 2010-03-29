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

module Env : sig
  type t
  val empty : t

  val rlookup : t -> Name.t -> Ty.t
  val elookup : t -> Name.t -> Ty.t
  val add_region_list : t -> Name.t list -> t * Name.t list
  val add_effect_var_list : t -> Name.t list -> t * Name.t list
  val add_var : t -> Name.t -> Ty.scheme -> t
  val lookup : t -> Name.t -> Ty.scheme
end = struct

  module M = Name.M
  type t =
    { r : Ty.t M.t ; e : Ty.t M.t ; n : Ty.scheme M.t }

  let empty =
    { r = M.empty ; e = M.empty; n = M.empty }

  let rlookup env t = M.find t env.r
  let elookup env t = M.find t env.e

  let add_region env x =
    { env with r = M.add x (Ty.var x) env.r }

  let add_effect_var env x =
    { env with e = M.add x (Ty.var x) env.e }

  let add_region_list env l =
    List.fold_left add_region env l, l

  let add_effect_var_list env l =
    List.fold_left add_effect_var env l, l

  let add_var env n s =
(*     Myformat.printf "adding: %a : %a@." Name.print n Ty.print_scheme s; *)
    { env with n = M.add n s env.n }

  let lookup env n =
    M.find n env.n

end

open Ast

let effect_lists_to_type_list env (rl,el) =
  let rt = List.map (fun x -> Ty.region (Env.rlookup env x)) rl in
  let et = List.map (Env.elookup env) el in
  rt@et

let effect_to_tuple_type env eff =
  Ty.tuple (effect_lists_to_type_list env (Effect.to_lists eff))

let get_to_select reg ref dom m l =
  let rl, _ = Effect.to_lists dom in
  let i = ExtList.find_pos Name.equal reg rl + 1 in
  ref_get (get_tuple i m l) ref l

let tyfun env =
  let f t : Ty.t =
    match t with
    | Ty.Map e -> effect_to_tuple_type env e
    | Ty.Ref (r,t) -> Ty.refty (Env.rlookup env r) t
    | _ -> t in
  Ty.node_map f

let genfun env (tl,rl,el) =
  let env, rl = Env.add_region_list env rl in
  let env,el = Env.add_effect_var_list env el in
  env, (tl@rl@el,[],[])

let scheme env (g, t) =
  let env, g = genfun env g in
  g, tyfun env t

let find_type t =
  let rec aux acc in_t =
    if Ty.equal in_t t then acc
    else
      match in_t with
      | Ty.Tuple tl ->
          aux_tup acc tl
      | _ -> raise Not_found
  and aux_tup' acc i tl =
    match tl with
    | [] -> raise Not_found
    | x::xs ->
        try aux (i::acc) x
        with Not_found -> aux_tup' acc (i+1) xs
  and aux_tup acc tl = aux_tup' acc 1 tl in
  aux_tup []

let build_get_tuple il tup l =
  List.fold_right (fun i acc -> get_tuple i acc l) il tup

let obtain_get t tl tup l =
(*
  Myformat.printf "--searching %a in list %a@."
    Ty.print t (Ty.print_list Myformat.comma) tl ;
*)
  let il = find_type t tl in
(*
  Myformat.printf "for type %a, found list: %a@." Ty.print t
    (Myformat.list Myformat.comma Myformat.int) il;
*)
  build_get_tuple il tup l

let adapt_tuples t tl1 t2 l =
  (* [t] is a tuple of list tl1, but we want a tuple of list tl2 *)
(*
  Myformat.printf "-have types %a, but want type %a@."
  (Ty.print_list Myformat.comma) tl1 Ty.print t2;
*)
  match t2 with
  | Ty.Tuple tl2 ->
      mk_tuple (List.length tl2)
        (List.map (fun t2 -> obtain_get t2 tl1 t l) tl2) l
  | _ -> obtain_get t2 tl1 t l

let adapt obt exp t l =
  (* [t] has type [obt], but we want it to have type [ext] *)
  let rec adapt obt exp t =
(*
    Myformat.printf "have type %a, but want type %a, and term %a has type %a@."
    Ty.print obt Ty.print exp print t Ty.print t.t;
*)
    if Ty.equal obt exp then t
    else
      match obt, exp with
      | Ty.PureArr (ta1,ta2), Ty.PureArr (tb1,tb2) ->
          plamho tb1 (fun x ->
            let x' = adapt tb1 ta1 x in
(*             Myformat.printf "adapted: %a@." print x'; *)
            adapt ta2 tb2 (app t x' l)) l
          (* if there is an order problem, it *has* to be a tuple on the left
           * side; otherwise, the types cannot be different *)
      | Ty.Tuple tl1, t2 -> adapt_tuples t tl1 t2 l
      | _, _ -> assert false
  in
  adapt obt exp t

let rec term env t =
  let l = t.loc in
  match destruct_get t with
  | Some (_,ref,reg,dom,m) ->
      let m = term env m in
      let ref = term env ref in
      get_to_select reg ref dom m l
  | _ ->
      match t.v with
      | Const _ -> t
      | App (f1,f2,k,c) ->
          app ~kind:k ~cap:c (term env f1) (term env f2) l
      | Var (v,(tl,rl,el)) ->
          let rl = List.map (Env.rlookup env) rl in
          let el = List.map (effect_to_tuple_type env) el in
          let tl = tl@(rl@el) in
          (* expected-type is the type of the object we want to have here;
           * we simply use its original type in the effect system and convert it
           * *)
          let expected_type = tyfun env t.t in
          let ni = (tl, [], []) in
          (* the obtained type is the type of the instantiated f in the new type
             system, maybe we have to convert *)
          let v = var v ni (scheme env (Env.lookup env v)) l in
          let obtained_type = v.t in
(*
          Myformat.printf "calling adapt with obt: %a; exp : %a; term %a of type
          %a@." Ty.print obtained_type Ty.print expected_type print v Ty.print
          v.t;
*)
          adapt obtained_type expected_type v l
      | Quant (k,t,b) ->
          let x,f = vopen b in
          let env = Env.add_var env x (Ty.Generalize.empty,t) in
          squant k x (tyfun env t) (term env f) l
      | Gen (g,t) ->
          let env, g = genfun env g in
          gen g (term env t) l
      | PureFun (t,b) ->
          let x,f = vopen b in
          plam x (tyfun env t) (term env f) l
      | Ite (e1,e2,e3) ->
          ite (term env e1) (term env e2) (term env e3) l
      | Let (g ,e1,b,r) ->
          let x,e2 = vopen b in
          let env', g = genfun env g in
          let e1 = term env' e1 in
          let_ g e1 x (term env e2) r l
      | Lam _ | LetReg _ | Param _ | HoareTriple _ ->
          assert false

let rec decl env d =
  match d with
  | Logic (n,g,t) ->
      let env' = Env.add_var env n (g,t) in
      let g,t = scheme env (g, t) in
      env', Logic (n,g,t)
  | Formula (s,t,k) ->
      env, Formula (s, term env t, k)
  | Section (s,cl,th) -> env, Section (s,cl, theory env th)
  | TypeDef (g,d,n) ->
      let _, g = genfun env g in
      env, TypeDef (g,d,n)
  | Program _ -> assert false
  | DLetReg rl ->
      let env, g = genfun env ([],rl,[]) in
      env, DGen g
  | DGen (tl,rl,el) ->
      let env, rl = Env.add_region_list env rl in
      let env,el = Env.add_effect_var_list env el in
      env, DGen (tl@rl@el,[],[])
and theory env t = snd (ExtList.fold_map decl env t)

let theory = theory Env.empty
