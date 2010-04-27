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
  | PureFunctionWithEffect
exception Error of Loc.loc * error

let explain e =
  match e with
  | UndeterminedType -> "cannot determine the type of this object."
  | PureFunctionWithEffect ->
      "pure functions should not have effects. Either remove the effects in \
        the function body or add pre/post annotations."

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

let recon_var loc v =
  let g,t = v.I.scheme in
  { var = v.I.var ; scheme = g, to_ty loc t;
    is_constr = v.I.is_constr; fix = v.I.fix }

let rec recon' loc = function
  | I.Var (x,i) -> Var (recon_var loc x,inst loc i)
  | I.Const c -> Const c
  | I.PureFun (x,t,e) ->
      let e = recon e in
      if not (Rw.is_empty e.e) then error loc PureFunctionWithEffect;
      PureFun (to_ty loc t,Name.close_bind x e)
  | I.App (e1,e2) -> App (recon e1, recon e2)
  | I.Quant (k,x,t,e) -> Quant (k,to_ty loc t, Name.close_bind x (recon e))
  | I.Lam (x,ot,(p,e,q)) -> Lam (x,ot, (recon p, recon e, recon q))
  | I.Param (t,e) -> Param (t,e)
  | I.Let (g,e1,x,e2,r) ->
      begin match r with
      | Const.Rec t -> LetRec (g, t, recclose x (recon e1) (recon e2))
      | Const.NoRec -> Let (g, recon e1, Name.close_bind x (recon e2))
      end
  | I.Ite (e1,e2,e3) -> Ite (recon e1, recon e2, recon e3)
  | I.For (dir,inv,i,st,en,body) ->
      let bdir = match dir with "forto" -> true|_ -> false in
      let body = recon body in
      let rw = body.e and l = body.loc in
      let inv = recon inv in
      let inv' = plam i Ty.int inv l in
      let intvar s = svar (mk_var_with_type false `Prefix s Ty.int) l in
      let cur = Name.from_string "cur" in
      let sv = intvar st and ev = intvar en and iv = intvar i in
      let read = Rw.reads rw and write = Rw.writes rw in
      let curvar = svar (mk_var_with_type false `Prefix cur (Ty.map read)) l in
      let pre =
        if bdir then
        (* forto: λcur. start <= i /\ i <= end_ /\ inv *)
          efflam cur read (and_ (encl sv iv ev l) (app inv curvar l) l) l
        else
        (* fordownto: λcur. end_ <= i /\ i <= start /\ inv *)
          efflam cur read (and_ (encl ev iv sv l) (app inv curvar l) l) l in
      let post =
        let next = if bdir then succ iv l else prev iv l in
        (* forto : λold.λcurλ(). inv (i+1) cur *)
        (* fordownto : λold.λcurλ(). inv (i-1) cur *)
        efflamho read (fun _ ->
          efflam cur read
            (plamho (Ty.unit ()) (fun _ ->
              app2 inv' next curvar l) l) l) l in
      let bodyfun = lam i Ty.int pre body post l in
      (* forvar inv start end bodyfun *)
      let read = Rw.reads_only rw in
      (app2 (app2 (predef dir ([],[],[read;write]) l) inv' sv l)
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
  | I.Case (t,bl) -> Case (recon t, List.map branch bl)
and get_pre (_,x) =
  match x with
  | None -> assert false
  | Some x -> recon x
and branch (nvl,p,t) = pclose nvl (pattern p) (recon t)
and pattern_node loc p =
  match p with
  | I.PVar v -> PVar v
  | I.PApp (v,i,pl) -> PApp (recon_var loc v, inst loc i, List.map pattern pl)
and pattern p =
  let loc = p.I.ploc in
  { pv = pattern_node loc p.I.pv; pt = to_ty loc p.I.pt; ploc = loc}
and recon (t : InferTree.t) : Ast.t =
  let loc = t.I.loc in
  { v = recon' loc t.I.v; t = to_ty loc t.I.t;
    e = to_rw loc t.I.e; loc = loc }
and inst loc i = Inst.map (to_ty loc) (to_region loc) (to_effect loc) i
let rec recon_decl x =
  match x with
  | I.Logic (x,g,t,f) ->
(*       Myformat.printf "found logic: %a, infix: %b@." Name.print x (f =
  *       `Infix); *)
      let s = g,t in
      Predefined.add_binding x (g,t,f);
      [Logic (x,s)]
  | I.Formula (s,t,k) -> [Formula (s, recon t, k)]
  | I.Section (s,cl, dl) -> [Section (s,recon_th dl, `Block cl)]
  | I.DLetReg rl -> [DLetReg rl]
  | I.TypeDef (n,tl,Abstract) -> [TypeDef (n,tl, Abstract)]
  | I.TypeDef (n,tl,ADT bl) -> [TypeDef (n,tl, ADT (List.map constbranch bl))]
  | I.Program (n,g,t,r,fix) ->
      let t = recon t in
      Predefined.add_binding n (g,t.t, fix);
      [Program (n,g,t, r)]
  | I.Fixpoint (n,g,t,e, fix) ->
      let e = recon e in
      let l = e.loc in
      Predefined.add_binding n (g,e.t, fix);
      let form =
        let acc, e = lambda_rev_destruct e in
        let tl = List.map (fun (x,t) ->
          let v = mk_var_with_type false `Prefix x t in
          svar v l) acc in
        let f =
          let v = mk_var_with_scheme false fix n (g,t) in
          var v (Ty.Generalize.to_inst g) l in
        let e = subst n (fun _ -> f) e in
        let fapp = List.fold_right (fun t acc -> app acc t l) tl f in
        let def = eq fapp e l in
        List.fold_left (fun acc (x,t) -> sforall x t acc l) def acc in
      [
        Logic (n,(g,t));
        Formula (Name.append n "def", gen g form l, `Assumed)
      ]

  | I.Inductive (n,g,t,tel) ->
      Predefined.add_binding n (g,t, `Prefix);
      let tel = List.map (fun (n,b) -> n, recon b) tel in
      [Inductive (n,g,t,tel)]
  | I.DGen g -> [DGen g]
and recon_th l = List.flatten (List.map recon_decl l)
and constbranch (n,tl) = n, tl

let theory th =
  recon_th th
