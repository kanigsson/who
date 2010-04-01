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
module I = InferTree
module M = MutableType

type error =
  | UndeterminedType
exception Error of Loc.loc * error

let explain e =
  match e with
  | UndeterminedType -> "cannot determine the type of this object."

let error loc k = raise (Error (loc,k))

let to_ty loc t =
  try M.to_ty t
  with MutableType.UndeterminedType -> error loc UndeterminedType

let to_region loc t =
  try M.to_region t
  with MutableType.UndeterminedType -> error loc UndeterminedType

let to_effect loc t =
  try M.to_effect t
  with MutableType.UndeterminedType -> error loc UndeterminedType

let to_rw loc t =
  try M.to_rw t
  with MutableType.UndeterminedType -> error loc UndeterminedType

let rec recon' loc = function
  | I.Var (x,i) -> Var (x,inst loc i)
  | I.Const c -> Const c
  | I.App (e1,e2,k,cap) -> App (recon e1, recon e2,k,cap)
  | I.PureFun (t,(s,x,e)) -> PureFun (to_ty loc t,(s,x, recon e))
  | I.Quant (k,t,(s,x,e)) -> Quant (k,to_ty loc t,(s,x, recon e))
  | I.Lam (x,ot,cap,(p,e,q)) -> Lam (x,ot, cap, (recon p, recon e, recon q))
  | I.Param (t,e) -> Param (t,e)
  | I.Let (g,e1,(_,x,e2),r) ->
      Let (g, recon e1, Name.close_bind x (recon e2),r)
  | I.Ite (e1,e2,e3) -> Ite (recon e1, recon e2, recon e3)
  | I.For (dir,inv,i,st,en,body) ->
      let bdir = match dir with {Name.name = Some "forto"} -> true|_ -> false in
      let body = recon body in
      let rw = body.e and l = body.loc in
      let e = Rw.overapprox rw in
      let inv = recon inv in
      let inv' = plam i Ty.int inv l in
      let intvar s = svar s Ty.int l in
      let cur = Name.from_string "cur" in
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
            (plam (Name.new_anon ()) (Ty.unit ())
              (app2 inv' next curvar l) l) l) l in
      let bodyfun = lam i Ty.int pre body post l in
      (* forvar inv start end bodyfun *)
      (app2 (app2
        (var dir ([],[],[e]) (Ty.forty ()) l) inv' sv l)
        ev bodyfun l).v
  | I.HoareTriple (p,e,q) -> HoareTriple (recon p, recon e, recon q)
(*
      let f = recon f and x = recon x and p = get_pre p and q = get_post q in
      let l = f.loc in
      let _,t2, e = Ty.from_logic_tuple f.t in
      let f =
        effFA e (fun m -> effFA e (fun n -> forall t2 (fun r ->
          let lhs = impl (app p m l) (applist [AR.pre f l; x; m] l) l in
          let rhs =
            impl (applist [AR.post f l; x; m ; n; r] l)
              (applist [q;m;n;r] l) l in
          and_ lhs rhs l) l) l) l in
      f.v
*)
  | I.LetReg (vl,e) -> LetReg (vl,recon e)
  | I.Annot (e,t) -> (recon e).v
  | I.Gen (g,e) -> Gen (g,recon e)
and get_pre (_,x) =
  match x with
  | None -> assert false
  | Some x -> recon x
and recon (t : InferTree.t) : Ast.t =
  let loc = t.I.loc in
  { v = recon' loc t.I.v; t = to_ty loc t.I.t;
    e = to_rw loc t.I.e; loc = loc }
and inst loc i = Inst.map (to_ty loc) (to_region loc) (to_effect loc) i
let rec recon_decl x =
  match x with
  | I.Logic (x,g,t) ->
      let s = g,t in
      Predefined.add_binding x s;
      Logic (x,s)
  | I.Formula (s,t,k) -> Formula (s, recon t, k)
  | I.Section (s,cl, dl) -> Section (s,recon_th dl, `Block cl)
  | I.DLetReg rl -> DLetReg rl
  | I.TypeDef (tl,n) -> TypeDef (tl,n)
  | I.Program (n,g,t,r) ->
      let t = recon t in
      Predefined.add_binding n (g,t.t);
      Program (n,g,t, r)
  | I.DGen g -> DGen g
and recon_th l = List.map recon_decl l

let theory = recon_th
