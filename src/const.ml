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

type t =
  | Int of Big_int.big_int
  | Ptrue
  | Pfalse

type ty =
  | TInt
  | TProp

type 'a isrec =
  | LogicDef
  | NoRec
  | Rec of 'a

type fix = Infix | Prefix

let type_of_constant = function
  | Int _ -> TInt
  | Ptrue | Pfalse -> TProp

type prover = [`Coq | `Pangoline | `Who ]
type takeover = prover * choice
and choice =
  | Include of string
  | TakeOver
  | Predefined

open Myformat
let print kind fmt = function
  | Int b -> string fmt (Big_int.string_of_big_int b)
  | Ptrue ->
      begin match kind with
      | `Pangoline -> string fmt "true"
      | _ -> string fmt "True"
      end
  | Pfalse ->
      begin match kind with
      | `Pangoline -> string fmt "false"
      | _ -> string fmt "False"
      end

let funsep fmt kind =
  match kind with
  | `Who | `Pangoline -> string fmt "->"
  | `Coq -> string fmt "=>"

let print_ty kind fmt = function
  | TInt ->
      begin match kind with
      | `Coq -> string fmt "Z"
      | _ -> string fmt "int"
      end
  | TProp ->
      match kind with
      | `Coq -> string fmt "Prop"
      | _ -> string fmt "prop"

let quant fmt = function
  | `FA -> string fmt "forall"
  | `EX -> string fmt "exists"

let quantsep fmt kind =
  match kind with
  | `Who | `Pangoline -> string fmt "."
  | `Coq -> string fmt ","

let prover fmt = function
  | `Pangoline -> string fmt "pangoline"
  | `Coq -> string fmt "coq"
  | `Who -> string fmt "who"
let choice fmt = function
  | Predefined -> string fmt "predefined"
  | Include s -> printf "\"%s\"" s
  | TakeOver -> string fmt "takeover"
let takeover fmt (p,c) = fprintf fmt "%a %a" prover p choice c
let compare a b =
  match a,b with
  | Int i1, Int i2 -> Big_int.compare_big_int i1 i2
  | _, _ -> Pervasives.compare a b

let hash_t x = Hashtbl.hash x
let equal_t = (=)
