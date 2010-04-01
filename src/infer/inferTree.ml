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

(* TODO adapt types of pre and post *)

module G = Ty.Generalize
module M = MutableType
type t' =
  | Const of Const.t
  | Var of Name.t * (M.t,M.r, M.effect) Inst.t
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t * [`Infix | `Prefix ] * Name.t list
  | Lam of Name.t * Ty.t * Name.t list * funcbody
  | Let of G.t * t * t Name.bind * isrec
  | PureFun of M.t * t Name.bind
  | Ite of t * t * t
  | Annot of t * Ty.t
  | Quant of [`FA | `EX ] * M.t * t Name.bind
  | Param of Ty.t * Effect.t
  | Gen of G.t * t
  | For of Name.t * pre * Name.t * Name.t * Name.t * t
  | HoareTriple of funcbody
  | LetReg of Name.t list * t
and t = { v : t' ; t : M.t ;
          e : M.effect ; loc : Loc.loc }
and post = t
and pre = t
and isrec = Ty.t Const.isrec
and funcbody = pre * t * post

type decl =
  | Logic of Name.t * G.t * Ty.t
  | Formula of Name.t * t * [ `Proved | `Assumed ]
  | Section of Name.t * Const.takeover list * decl list
  | TypeDef of Name.t list * Name.t
  | Program of Name.t * G.t * t * isrec
  | DLetReg of Name.t list
  | DGen of G.t

type theory = decl list

let mk v t e loc = { v = v; t = t; e = e; loc = loc }
let mk_val v t = mk v t M.eff_empty
let const c = mk_val (Const c) (M.const (Const.type_of_constant c))

let pure_lam x t e =
  mk_val (PureFun (t, Name.close_bind x e)) (M.parr t e.t)

let annot e t = mk (Annot (e,t)) e.t e.e
