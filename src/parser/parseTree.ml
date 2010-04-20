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

(* This module represents the parse tree *)
module C = Const
type var = string
type rvar = string
type effvar = string
type tvar = string

type effect = ParseTypes.effect
type rw = ParseTypes.rw
type ty = ParseTypes.t

type inst = ty list * rvar list * effect list

type t' =
  | Const of Const.t
  | Var of var * inst
  | App of t * t * [`Infix | `Prefix ]
  | Seq of t * t
  | Lam of var option * ty * t option * t * post
  | Let of generalize * t * var * t * ty Const.isrec
  | PureFun of var option * ty option * t
  | Ite of t * t * t
  | Annot of t * ty
  | Quant of [`FA | `EX] * var option * ty option * t
  | Param of ty * rw
  | For of var * t option * var * t * t * t
  | LetReg of rvar list * t
  | Restrict of t * effect
  | Get of t * t
  | Ref of rvar
  | HoareTriple of t option * t * post
  | Case of t * branch list
  | Gen of generalize * t
and t = t' Loc.t
and post =
  | PNone
  | PPlain of t
  | PResult of var * t
and generalize = tvar list * rvar list * effvar list
and branch = pattern * t
and pattern_node =
  | PVar of string option
  | PApp of string * pattern list
and pattern = { pv : pattern_node ; ploc : Loc.loc }

type decl =
  | Logic of var * generalize * ty
  | Axiom of string * generalize * t
  | Goal of string * generalize * t
  | Section of var * Const.takeover list * decl list
  | TypeDef of var * generalize * typedef
  | Program of var * generalize * t * ty Const.isrec
  | Inductive of var * generalize * ty list * t list
  | DLetReg of rvar list
and typedef =
  | Abstract
  | Alias of ty
  | ADT of constbranch list
and constbranch = var * ty list

type theory = decl list

let app ?(kind=`Prefix) t1 t2 pos = Loc.mk pos (App (t1,t2, kind))
let var ?(inst=([],[],[])) s pos = Loc.mk pos (Var (s,inst))
let const c pos = Loc.mk pos (Const c)
let app2 s t1 t2 loc = app (app (var s loc) t1 loc) t2 loc
let appi s t1 t2 loc = app ~kind:`Infix (app (var s loc) t1 loc) t2 loc

let appn t1 tl =
  List.fold_left (fun t1 t2 -> app t1 t2 (Loc.join_with t1 t2)) t1 tl

let appni s tl loc = appn (var s loc) tl

let let_ l e1 x e2 r pos = Loc.mk pos (Let (l,e1,x,e2,r))
let lam x t p e q pos = Loc.mk pos (Lam (x,t,p,e,q))
let pure_lam x t e pos = Loc.mk pos (PureFun (x,t,e))
let quant k x t e pos = Loc.mk pos (Quant (k,x,t,e))

