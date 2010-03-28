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

open Name
open Const
open Ast
open Recon
module PL = Predefined
module PI = Predefined.Identifier

exception Error of string

let error s = Myformat.ksprintf (fun s -> raise (Error s)) s

module NPair = struct
  type t = Name.t * Name.t
  let compare = Pair.compare Name.compare Name.compare
end

module NPM = Map.Make(NPair)

(* rtypes : returns a type for a region name
   renames : retuns a unique name for a couple (region, state)
   et : current type
   l : current location
*)
type env =
  { rtypes : Ty.t Name.M.t ;
    renames : Name.t NPM.t;
    et : Ty.t;
    l : Loc.loc
  }

let empty =
  { rtypes = Name.M.empty ; renames = NPM.empty; et = Ty.int; l = Loc.dummy }


  (* [rtype_add] adds a type for a given region name *)
let rtype_add n t env =
  { env with rtypes = Name.M.add n t env.rtypes }

  (* [rtype] finds the type for a region name *)
let rtype env n =
  try Name.M.find n env.rtypes
  with Not_found ->
    failwith
    (Myformat.sprintf "type not found for region: %a@."
      Name.print n)

let cannot_find_type n =
  error "finding no type for %a@." Name.print n

(* [find_type] searches for a [tau ref(r)] in the given term *)
let find_type rname x =
(*   Myformat.printf "find_type: %a in %a@." Name.print rname print x; *)
  let rec aux x =
    match Ty.find_type_of_r rname x.t with
    | Some x -> x
    | None ->
        match x.v with
        | Quant (_,t,b)
        | PureFun (t,b) ->
            begin match Ty.find_type_of_r rname t with
            | Some x -> x
            | None ->
                let _,e = sopen b in
                aux e
            end
        | Gen (_,t) -> aux t
        | App (t1,t2,_,_) ->
            begin try aux t1
            with _ -> aux t2 end
        | _ -> assert false in
  try aux x with Assert_failure _ -> cannot_find_type rname

let rec find_type_decl rname th =
  match th with
  | [] -> cannot_find_type rname
  | d::ds ->
      match d with
      | Logic (_,_,t) ->
          begin match Ty.find_type_of_r rname t with
          | Some x -> x
          | None -> find_type_decl rname ds
          end
      | _ -> cannot_find_type rname

(* add the mapping (n1,n2) -> n3 to the environment for names
 * n1: region
 * n2: state
 * n3: fresh name
 * *)

let name_add n1 n2 n3 env =
  { env with renames = NPM.add (n1,n2) n3 env.renames; }

(* find the name corresponding to (n1,n2) *)
let getname n1 n2 env =
  try NPM.find (n1,n2) env.renames
  with Not_found ->
    failwith
    (Myformat.sprintf "name not found in state: %a, %a@."
      Name.print n1 Name.print n2)

(* for region [r] and state [v], build the term variable using the fresh name
 * corresponding to (r,v) *)
let build_var r v env =
  try
    let nv = getname r v env in
    svar nv (rtype env r) env.l
  with Not_found ->
    error "did not find a fresh variable for : (%a,%a)@." Name.print r
    Name.print v


(* for effect var [e] and state [v], build the term variable using the fresh
 * name corresponding to (r,v) - an effect variable is its own type *)
let build_evar e v env =
  let nv = getname e v env in
  svar nv (Ty.var e) env.l

(* a simplification either does nothing, a simple top-level change, or a deeper
 * change requiring all simplifications to rerun *)
let tyfun env t = Ty.selim_map (rtype env) t

let add_effect env x d =
(*   Myformat.printf "adding effect : %a@." Effect.print d; *)
  let env,rl =
    Effect.rfold (fun r (env,rl) ->
      let n = Name.new_name r in
      name_add r x n env, (n,rtype env r)::rl) (env,[]) d in
  let env, el =
    Effect.efold (fun e (env,el) ->
      let n = Name.new_name e in
      name_add e x n env, (e,n)::el) (env,[]) d in
  env, rl,el

let rec term env t =
  let l = t.loc in
  match destruct_get t with
  | Some (_,_,reg,dom,m) ->
      begin try
        let t = Effrec.from_form dom m in
        let nf = build_var reg (Effrec.get_reg reg t) env in
        nf
      with Not_found ->
        error "did not find ref %a in %a@." Name.print reg print m;
      end
  | _ ->
      match t.v with
      | Const _ -> t
      | App (t1,t2,_,_) when Ty.is_map t2.t ->
          let t1 = term env t1 in
          let er = Effrec.from_form_t t2.t t2 in
          let t1 = {t1 with t = Ty.selim_map (rtype env) t1.t} in
          let f = Effrec.rfold (fun r s acc ->
            app acc (build_var r s env) l) er t1 in
          let f = Effrec.efold (fun e s acc ->
            app acc (build_evar e s env) l) er f in
          f
      | Var (v,i) ->
          var_i v (Inst.map (tyfun env) Misc.id Misc.id i) (tyfun env t.t) l
      | App (f1,f2,k,c) ->
          app ~kind:k ~cap:c (term env f1) (term env f2) l
      | Gen (g,t) ->
          let env, g = genbind g env (fun r -> find_type r t) in
          let t = term env t in
          gen g t env.l
      | Let (g ,e1,b,r) ->
          let x,e2 = vopen b in
          let env', g = genbind g env (fun r -> find_type r e1) in
          let e1 = term env' e1 in
          let_ g e1 x (term env e2) r l
      | PureFun (t,b) ->
          let x,e = vopen b in
          varbind env `LAM x t e l
      | Quant (k,t,b) ->
          let x,e = vopen b in
          varbind env (k :> [`EX | `FA | `LAM ]) x t e l
      | Ite (e1,e2,e3) ->
          ite (term env e1) (term env e2) (term env e3) l
      | Lam _ | LetReg _ | Param _ | HoareTriple _ ->
          assert false
and genbind (tvl,rl,el) env find_type =
    let env = List.fold_left (fun env r ->
      rtype_add r (find_type r) env) env rl in
    let env = List.fold_left (fun env e ->
      rtype_add e (Ty.var e) env) env el in
    env, (tvl@el,[],[])
(*
    let t = term env t in
    (* effect variables become type variables *)
    (tvl@el,[],[]), t
*)
and varbind env k x t e l =
  if Ty.is_map t then
    let env, rl, el = add_effect env x (Ty.domain t) in
    let e = term env e in
    let f = List.fold_left (fun acc (x,t) -> aquant k x t acc l) e rl in
      List.fold_left (fun acc (old,new_) ->
        aquant k new_ (rtype env old) acc l) f el
  else
    let e = term env e in
    if Ty.is_ref t then e
    else aquant k x (Ty.selim_map (rtype env) t) e l

let effrec_set = [ PI.empty_id ; PI.restrict_id ; PI.get_id ; PI.combine_id ]

let rec theory env th =
  match th with
  | [] -> env, []
  | d :: ds ->
      let env, d =
        match d with
        | Logic (n,_,_) when PL.belongs_to n effrec_set -> env, []
        | Logic (s,((_,[],[]) as g),t) ->
            (*       Myformat.printf "%a@." Name.print s; *)
            env, if Ty.is_ref t then [] else [Logic (s,g,tyfun env t)]
        | DGen g ->
            let env, g = genbind g env (fun r -> find_type_decl r ds) in
            env, if G.is_empty g then [] else [DGen g]
        | TypeDef _ -> env, [d]
        | Formula (n,f,k) ->
            env, [Formula (n, term env f, k)]
        | Section (s,cl,th) ->
            let env, th = theory env th in
            env, if th = [] then [] else [Section (s,cl,th)]
        | Program (n,g,t,LogicDef) ->
            let env', g = genbind g env (fun r -> find_type r t) in
            let t = term env' t in
            env, [Program (n,g,t,LogicDef)]
        | Program _ | Logic _ | DLetReg _ -> assert false in
      let env, th = theory env ds in
      env, d @ th

let theory th =
  let _, th = theory empty th in
  th

