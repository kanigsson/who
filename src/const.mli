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

type ty = 
  | TInt
  | TProp


type t = 
  | Int of Big_int.big_int
  | Ptrue
  | Pfalse

val equal_t : ty -> ty -> bool
val hash_t : ty -> int

val compare : t -> t -> int

val type_of_constant : t -> ty

type 'a isrec = 
  | LogicDef
  | NoRec
  | Rec of 'a

type takeover = [`Coq | `Pangoline ] * choice
and choice = 
  | Include of string
  | TakeOver 
  | Predefined

val print_ty : [`Coq | `Who | `Pangoline ] -> ty Myformat.fmt
val print : t Myformat.fmt
val funsep : [`Coq | `Who | `Pangoline ] Myformat.fmt
val quant : [`FA | `EX ] Myformat.fmt
val quantsep : [`Coq | `Who | `Pangoline ] Myformat.fmt
val takeover : takeover Myformat.fmt

