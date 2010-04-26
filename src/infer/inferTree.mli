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

type var =
  { var : Name.t;
    scheme : Ty.Generalize.t * MutableType.t;
    is_constr : bool;
    fix : [`Prefix | `Infix ]
  }

type t' =
  | Const of Const.t
  | Var of var * inst
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t
  | Lam of Name.t * Ty.t * funcbody
  | Let of Ty.Generalize.t * t * Name.t * t * isrec
  | PureFun of Name.t * MutableType.t * t
  | Ite of t * t * t
  | Annot of t * Ty.t
  | Quant of [`FA | `EX ] * Name.t * MutableType.t * t
  | Param of Ty.t * Rw.t
  | Gen of Ty.Generalize.t * t
  | For of string * pre * Name.t * Name.t * Name.t * t
  | HoareTriple of funcbody
  | LetReg of Name.t list * t
  | Case of t * branch list
and t = { v : t' ; t : MutableType.t ;
          e : MutableType.rw ; loc : Loc.loc }
and post = t
and pre = t
and isrec = Ty.t Const.isrec
and funcbody = pre * t * post
and branch = Name.t list * pattern * t
and inst = (MutableType.t,MutableType.r, MutableType.effect) Inst.t
and pattern_node =
  | PVar of Name.t
  | PApp of var * inst * pattern list
and pattern = { pv : pattern_node ; pt : MutableType.t ; ploc : Loc.loc}


type decl =
  | Logic of Name.t * Ty.Generalize.t * Ty.t * [`Infix | `Prefix ]
  | Formula of Name.t * t * [ `Proved | `Assumed ]
  | Section of Name.t * Const.takeover list * decl list
  | TypeDef of Name.t * Name.t list * Ast.typedef
  | Program of Name.t * Ty.Generalize.t * t * isrec * [`Infix | `Prefix ]
  | Fixpoint of Name.t * Ty.Generalize.t * Ty.t * t * [`Infix | `Prefix ]
  | DLetReg of Name.t list
  | Inductive of Name.t * Ty.Generalize.t * Ty.t * inductive_branch list
  | DGen of Ty.Generalize.t
and inductive_branch = Name.t * t

type theory = decl list

val pure_lam : Name.t -> MutableType.t -> t -> Loc.loc -> t
