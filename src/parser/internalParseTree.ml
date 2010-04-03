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

module G = Ty.Generalize

(** TODO declare some type annotations as optional *)

type t' =
  | Const of Const.t
  | Var of Name.t * Effect.t list
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t * [`Infix | `Prefix ] * Name.t list
  | Lam of Name.t * Ty.t * Name.t list * funcbody
  | Let of G.t * t * t Name.bind * isrec
  | PureFun of MutableType.t option * t Name.bind
  | Ite of t * t * t
  | Annot of t * Ty.t
  | Quant of [`FA | `EX ] * MutableType.t option * t Name.bind
  | Param of Ty.t * Rw.t
  | Gen of G.t * t
  | For of string * pre * Name.t * Name.t * Name.t * t
  | HoareTriple of funcbody
  | LetReg of Name.t list * t
  | Restrict of t * Effect.t
  | Get of t * t
and t = { v : t' ; loc : Loc.loc }
and post' =
  | PNone
  | PPlain of t
  | PResult of Name.t * t
and pre = Name.t * t option
and post = Name.t * Name.t * post'
and isrec = Ty.t Const.isrec
and funcbody = pre * t * post

type decl =
  | Logic of Name.t * G.t * Ty.t
  | Formula of Name.t * t * [ `Proved | `Assumed ]
  | Section of Name.t * Const.takeover list * decl list
  | TypeDef of Name.t list * Name.t
  | Program of Name.t * G.t * t * isrec
  | Inductive of Name.t * G.t * Ty.t * t list
  | DLetReg of Name.t list
  | DGen of G.t

type theory = decl list

let mk t l = { v = t ; loc = l }
let annot e t = mk (Annot (e,t))
let gen g t l =
  if Ty.Generalize.is_empty g then t else mk (Gen (g,t)) l

let app t1 t2 = mk (App (t1,t2,`Prefix,[]))
let var ?(inst=[]) v = mk (Var (v,inst))

let print _ _ = assert false (* TODO *)

let ptrue l = mk (Const Const.Ptrue) l
let pure_lam x t e = mk (PureFun (t, Name.close_bind x e))
