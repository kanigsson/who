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

module I = Infer
open Ast
module AR = Ast.Recon
open AR

let rec recon' = function
  | Var (x,i) -> Var (x,inst i)
  | Const c -> Const c
  | App (e1,e2,k,cap) -> App (recon e1, recon e2,k,cap)
  | PureFun (t,(s,x,e)) -> PureFun (t,(s,x, recon e))
  | Quant (k,t,(s,x,e)) -> Quant (k,t,(s,x, recon e))
  | Lam (x,ot,cap,(p,e,q)) ->
      let e = recon e in
      Lam (x,ot, cap, (pre p, e, post q))
  | Param (t,e) -> Param (t,e)
  | Let (g,e1,(_,x,e2),r) ->
      Let (g, recon e1, Name.close_bind x (recon e2),r)
  | Ite (e1,e2,e3) -> Ite (recon e1, recon e2, recon e3)
  | For (dir,inv,i,st,en,body) ->
      let bdir = match dir with {Name.name = Some "forto"} -> true|_ -> false in
      let body = recon body in
      let e = body.e and l = body.loc in
      let cur,inv = pre inv in
      let inv = match inv with | None -> ptrue_ l | Some f -> f in
      let inv' = plam i Ty.int inv l in
      let intvar s = svar s Ty.int l in
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
            (plam (Name.new_anon ()) Ty.unit
              (app2 inv' next curvar l) l) l) l in
      let bodyfun = lam i Ty.int (cur,Some pre) body (old,cur,PPlain post) l in
      (* forvar inv start end bodyfun *)
      (app2 (app2 (var dir ([],[],[e]) Ty.forty l) inv' sv l) ev bodyfun l).v
  | HoareTriple (p,e,q) -> HoareTriple (pre p, recon e, post q)
(*
      let f = recon f and x = recon x and p = get_pre p and q = get_post q in
      let l = f.loc in
      let _,t2, e = Ty.from_logic_tuple f.t in
      let f =
        effFA e (fun m -> effFA e (fun n -> forall t2 (fun r ->
          let lhs = impl (app p m l) (applist [AR.pre f l; x; m] l) l in
          let rhs =
            impl (applist [AR.post f l; x; m ; n; r] l) (applist [q;m;n;r] l) l in
          and_ lhs rhs l) l) l) l in
      f.v
*)
  | LetReg (vl,e) -> LetReg (vl,recon e)
  | Annot (e,t) -> Annot (recon e, t)
  | Gen (g,e) -> Gen (g,recon e)
and pre (cur,x) =
  match x with
  | None ->  assert false
  | Some x -> cur, Some (recon x)
and get_pre (_,x) =
  match x with
  | None -> assert false
  | Some x -> recon x
and get_post (_,_,x) =
  match x with
  | PPlain f -> recon f
  | _ -> assert false
and recon (t : Ast.Infer.t) : Ast.Recon.t =
  { v = recon' t.v; t = U.to_ty t.t; e = U.to_eff t.e; loc = t.loc }
and inst i = Inst.map U.to_ty U.to_r U.to_eff i
and post (old,cur,x) =
  let p = match x with
  | PNone -> assert false
  | PPlain f -> PPlain (recon f)
  | _ -> assert false in
  old, cur, p

let rec recon_decl x =
  match x with
  | Logic (x,g,t) -> Logic (x,g,t)
  | Formula (s,t,k) -> Formula (s, recon t, k)
  | Section (s,cl, dl) -> Section (s,cl, recon_th dl)
  | DLetReg rl -> DLetReg rl
  | TypeDef (g,t,n) -> TypeDef (g,t,n)
  | Program (n,g,t,r) -> Program (n,g,recon t, r)
  | DGen g -> DGen g
and recon_th l = List.map recon_decl l

let prelude, prelude_table = 
  let p = recon_th I.prelude in
  let table = build_symbol_table p in
  Predefined.Logic.init table;
  p, table

let theory = recon_th
