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
open Recon
module G = Ty.Generalize

exception Error of string * Loc.loc
let error s loc = raise (Error (s,loc))

let ty = Ty.to_logic_type

let efflamho = efflamho ~s:"s"
let plamho = plamho ~s:"r"
let effFA = effFA ~s:"s"

let lift_scheme (g,t) = g, ty t

let lift_var v =
  { v with scheme = lift_scheme v.scheme; }

let lift_inst i = Inst.map ty Misc.id Misc.id i

let rec lift_value v =
  let l = v.loc in
  match v.v with
  | Var (v,i) -> var (lift_var v) (lift_inst i) l
  | Const _ -> v
  | App (v1,v2) -> app (lift_value v1) (lift_value v2) l
  | PureFun (t,(_,x,e)) ->
      plam x (ty t) (lift_value e) l
  | Quant (k,t,(_,x,e)) ->
      squant k x (ty t) (lift_value e) l
  | Lam (x,t,(p,_,q)) ->
      let t = ty t in
      let p = plam x t (scan p) l and q = plam x t (scan q) l in
      mk_pair p q l
  | Let (g,e1,b,Const.LogicDef) ->
      let x,f = vopen b in
      let_ g (lift_value e1) x (lift_value f) Const.LogicDef l
  | Case (t,bl) ->
      case (lift_value t) (List.map lift_branch bl) l
  | HoareTriple (p,e,q) -> bodyfun p e q
  | Let _ | LetReg _ | Gen _ | Param _ | Ite _  ->
      error (Myformat.sprintf "not a value: %a" print v) l
and lift_branch b =
  let nvl, p, t = popen b in
  pclose nvl p (lift_value t)

and correct v =
  let l = v.loc in
  match v.v with
  | Var _ | Const _ | Quant _ -> ptrue_ l
  | App (v1,v2) -> and_ (correct v1) (correct v2) l
  | Lam (x,t,(p,e,q)) -> sforall x (ty t) (bodyfun p e q) l
  | PureFun (t,(_,x,e)) -> sforall x (ty t) (correct e) l
  | Let (g,e1,b,Const.LogicDef) ->
      let x,e2 = vopen b in
      and_ (gen g (correct e1) l)
        (let_ g (lift_value e1) x (correct e2) Const.LogicDef l) l
  | Case (t,bl) ->
      and_ (correct t) (case (lift_value t) (List.map branch_correct bl) l) l
  | Let _ | LetReg _ | Gen _ | Param _
  | Ite _ | HoareTriple _ ->
      Myformat.printf "correct: not a value: %a@." print v;
      assert false
and branch_correct b =
  let nvl, p, t = popen b in
  pclose nvl p (correct t)
and scan f =
  let termfun f =
    match f.v with
    | HoareTriple (p,e,q) -> bodyfun p e q
    | _ -> f in
  rebuild_map ~varfun:(fun _ _ def -> def) ~termfun ~tyfun:ty f
and bodyfun p e q =
  let l = e.loc in
  effFA (Rw.overapprox e.e) (fun r ->
    let p = app (scan p) r l
    and q = efflamho (Rw.writes e.e) (fun r2 ->
      applist [scan q; r; combine r r2 l] l) l in
    impl p (wp_node r q e) l) l
and wp m q e =
  let ft = ty e.t and l = e.loc in
  let write = Rw.writes e.e in
  if is_value e then
    and_ (applist [q;m;lift_value e] l) (correct e) l
  else
    match e.v with
    | LetReg (rl,se) ->
        let ef = Effect.from_lists rl [] in
        rgen rl
        (effFA ef (fun cur ->
          wp_node (combine m cur l)
            (efflamho (Effect.union (Rw.writes se.e) ef) (fun s ->
              app q (restrict write s l) l) l) se) l) l
    | App (v1,v2) ->
        let lv1 = lift_value v1 and lv2 = lift_value v2 in
        andlist
        [ correct v1; correct v2;
          applist [pre lv1 l; lv2; m ] l;
          effFA write (fun m2 ->
            let m2' = combine m m2 l in
            forall ft (fun x ->
              impl (applist [post lv1 l; lv2; m; m2'; x] l)
                (applist [q;m2; x] l) l) l) l ] l
    | Let (g,e1,b,Const.LogicDef) ->
        let x,e2 = vopen b in
        let f = wp_node m q e2 in
        let_ g e1 x f (Const.LogicDef) l
    | Let (g,e1,b,r) ->
        let x,e2 = vopen b in
        if is_value e1 then
          let lv = lift_value e1 in
          let f = gen g (correct e1) l in
          let wp = wp_node m q e2 in
          let gen f = let_ g lv x f Const.LogicDef l in
          match r with
          | Const.NoRec -> and_ f (gen wp) l
          | Const.Rec _ -> gen (and_ f wp l)
          | Const.LogicDef -> assert false
        else
          let t = ty e1.t in
          let f = efflamho write (fun m2 ->
            plam x t (wp_node (combine m m2 l) q e2) l) l in
          wp_node m f e1
    | Ite (c,th,el) -> ite (lift_value c) (wp_node m q th) (wp_node m q el) l
    | Case (v,bl) ->
        case (lift_value v) (List.map (branch m q) bl) l
    | Param _ -> ptrue_ l
    | _ -> assert false
and wp_node m q e =
(*   Myformat.printf "wp:%a@." print e; *)
  let read, write = Rw.read_write e.e in
  let writeq = Ty.domain (Ty.arg q.t) and l = e.loc in
  if Effect.equal write writeq then wp (restrict read m l) q e
  else
    wp (restrict read m l)
      (efflamho write (fun m2 ->
        app q (combine (restrict writeq m l) m2 l) l) l) e
and branch m q b =
  let nvl, p, e = popen b in
  pclose nvl p (wp_node m q e)


let main e =
  let l = e.loc in
  let read = Rw.reads e.e in
  let q = efflamho read (fun _ -> plamho e.t (fun _ -> ptrue_ l) l) l in
    effFA read (fun m -> (wp_node m q e)) l


let correct_name n = Name.append n "_correct"

let scheme (g,t) = g, ty t

let rec decl d =
  match d with
  | TypeDef _ | Inductive _
  | Program (_,_,_,Const.LogicDef) | DGen _ | Decl _ -> [d]
  | Logic (n,s) -> [ Logic (n,scheme s) ]
  | Formula (n,f,k) -> [Formula (n,scan f, k) ]
  | DLetReg rl ->
      (* FIXME is this correct? *)
      [DGen ([],rl,[])]
  | Section (s,dl, kind) -> [Section (s, theory dl, kind)]
  | Program (x,g,e,_) when is_value e ->
      (* TODO recursive functions *)
      let lv = lift_value e in
      let f = gen g (correct e) e.loc in
      let def = Program (x,g,lv, Const.LogicDef) in
      begin match mk_goal (correct_name x) f with
      | None -> [def]
      | Some goal -> [goal ; def ]
      end
  | Program _ -> assert false


and theory th =
  List.flatten (List.map decl th)

