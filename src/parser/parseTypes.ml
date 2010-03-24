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

type effect = string list * string list

type t =
  | TVar of string
  | TConst of Const.ty
  | Tuple of t list
  | Arrow of t * t * effect * string list
  | PureArr of t * t
  | TApp of string * (t,string,effect) Inst.t
  | Ref of string * t
  | Map of effect
  | ToLogic of t

open Myformat

let print fmt t =
  let rec pt fmt = function
  | TVar v -> pp_print_string fmt v
  | TConst c -> Const.print_ty `Who fmt c
  | Tuple tl -> paren (print_list (fun fmt () -> fprintf fmt " *@ ") pt) fmt tl
  | PureArr (t1,t2) -> fprintf fmt "(%a -> %a)" pt t1 pt t2
  | Arrow (t1,t2,_,_) -> fprintf fmt "(%a ->{...} %a)" pt t1 pt t2
  | Ref _ -> pp_print_string fmt "ref(...)"
  | Map _ -> pp_print_string fmt "<...>"
  | TApp (v,_) -> fprintf fmt "app(%s)" v
  | ToLogic t -> fprintf fmt "[[ %a ]]" pt t in
  pt fmt t
