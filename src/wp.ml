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

let rec lift_value v =
  let l = v.loc in
  match v.v with
  | Var (_,_) ->
      { v with t = ty v.t }
  | Const _ -> v
  | App (v1,v2,kind,_) ->
      app ~kind (lift_value v1) (lift_value v2) l
  | PureFun (t,(_,x,e)) ->
      plam x (ty t) (lift_value e) l
  | Quant (k,t,(_,x,e)) ->
      squant k x (ty t) (lift_value e) l
  | Lam (x,t,_,(p,_,q)) ->
      let t = ty t and _,p = p and _,_,q = q in
      let p =
        match p with
        | None -> assert false
        | Some p -> plam x t (scan p) l
      and q =
        match q with
        | PResult _ | PNone _ -> assert false
        | PPlain q -> plam x t (scan q) l in
      mk_tuple p q l
  | Let (g,e1,b,Const.LogicDef) ->
      let x,f = sopen b in
      let_ g (lift_value e1) x (lift_value f) Const.LogicDef l
  | HoareTriple (p,e,q) -> bodyfun p e q
  | Let _ | LetReg _ | For _ | Gen _ | Param _ | Annot _ | Ite _ ->
      error (Myformat.sprintf "not a value: %a" print v) l

and correct v =
  let l = v.loc in
  match v.v with
  | Var _ | Const _ | Quant _ -> ptrue_ l
  | App (v1,v2,_,_) -> and_ (correct v1) (correct v2) l
  | Lam (x,t,_,(p,e,q)) -> sforall x (ty t) (bodyfun p e q) l
  | PureFun (t,(_,x,e)) -> sforall x (ty t) (correct e) l
  | Let (g,e1,b,Const.LogicDef) ->
      let x,e2 = sopen b in
      and_ (gen g (correct e1) l)
        (let_ g (lift_value e1) x (correct e2) Const.LogicDef l) l
  | Let _ | LetReg _ | For _ | Gen _ | Param _ | Annot _ | Ite _ | HoareTriple _ ->
      Myformat.printf "correct: not a value: %a@." print v;
      assert false
and scan f =
  let termfun f =
    match f.v with
    | HoareTriple (p,e,q) -> bodyfun p e q
    | _ -> f in
  rebuild_map ~varfun:(fun _ _ def -> def) ~termfun ~tyfun:ty f
and bodyfun p e q =
  let l = e.loc in
  effFA e.e (fun r ->
    let p = match p with
    | _,None -> assert false
    | _,Some f -> app (scan f) r l in
    let q = match q with
    | _,_,(PNone | PResult _) -> assert false
    | _,_,PPlain f -> app (scan f) r l in
    impl p (wp_node r q e) l) l
and wp m q e =
  let ft = ty e.t and l = e.loc in
  if is_value e then
    and_ (applist [q;m;lift_value e] l) (correct e) l
  else
    match e.v with
    | LetReg (rl,se) ->
        let ef = Effect.from_lists rl [] in
        rgen rl
        (effFA ef (fun cur ->
          wp_node (combine m cur l)
            (efflamho (Effect.union se.e ef) (fun s ->
              app q (restrict e.e s l) l) l) se) l) l
    | App (v1,v2,_,_) ->
        let lv1 = lift_value v1 and lv2 = lift_value v2 in
        andlist
        [ correct v1; correct v2;
          applist [pre lv1 l; lv2; m ] l;
          effFA e.e (fun m2 ->
            forall ft (fun x ->
              impl (applist [post lv1 l; lv2; m; m2; x] l)
                (applist [q;m2; x] l) l) l) l ] l
    | Let (g,e1,b,Const.LogicDef) ->
        let x,e2 = sopen b in
        let f = wp_node m q e2 in
        let_ g e1 x f (Const.LogicDef) l
    | Let (g,e1,b,r) ->
        let x,e2 = sopen b in
        (* TODO recursive case *)
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
          let t = ty e1.t and eff = e.e in
          let f = efflamho eff (fun m2 ->
            plam x t (wp_node (combine m m2 l) q e2) l) l in
          wp_node m f e1
    | Ite (c,th,el) -> ite (lift_value c) (wp_node m q th) (wp_node m q el) l
    | Param _ -> ptrue_ l
    | _ -> assert false
and wp_node m q e =
(*   Myformat.printf "wp:%a@." print e; *)
  let r =
  if Effect.equal (domain m) e.e then wp m q e
  else begin
    let l = e.loc in
    wp (restrict e.e m l)
      (efflamho e.e (fun m2 -> app q (combine m m2 l) l) l)
      e
  end in
(*   Myformat.printf "--end@.";  *)
  r

let main e =
  let l = e.loc in
  let q = efflamho e.e (fun _ -> plamho e.t (fun _ -> ptrue_ l) l) l in
    effFA e.e (fun m -> (wp_node m q e)) l


let rec decl d =
  match d with
  | Logic _ | Formula _ | TypeDef _
  | Program (_,_,_,Const.LogicDef) | DGen _ -> [d]
  | DLetReg rl ->
      (* FIXME is this correct? *)
      [DGen ([],rl,[])]
  | Section (s,cl,dl) -> [Section (s,cl, theory dl)]
  | Program (x,g,e,_) when is_value e ->
      (* TODO recursive functions *)
      let lv = lift_value e in
      let f = gen g (correct e) e.loc in
      let def = Program (x,g,lv, Const.LogicDef) in
      begin match mk_goal (Name.unsafe_to_string x ^ "_correct") f with
      | None -> [def]
      | Some goal -> [goal ; def ]
      end
  | Program _ -> assert false


and theory th =
  List.flatten (List.map decl th)

