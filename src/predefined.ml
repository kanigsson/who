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

module SM = Misc.StringMap

let preinstantiated_tuple = 7

type error =
  | PreludeIncomplete of string

exception Error of error

let error e = raise (Error e)

let explain error =
  match error with
  | PreludeIncomplete s ->
      Myformat.sprintf "the prelude is incomplete; the following symbol is \
        missing: %s" s

open Identifiers

type env =
  {
    mutable ty_map : (Ty.Generalize.t * Ty.t) Name.M.t ;
    mutable name_map : Name.t Misc.StringMap.t
  }

let env =
  { ty_map = Name.M.empty ; name_map  = Misc.StringMap.empty }

let pangoline_predefined =
  [
    impl_id, "=>" ;
    not_id, "not" ;
    and_id, "and" ;
    or_id, "or" ;
    btrue_id, "btrue";
    bfalse_id, "bfalse";
  ] @
  (List.flatten
    (ExtList.repeat ~from:2 (preinstantiated_tuple + 1) (fun i ->
      ExtList.repeat ~from:1 (i + 1) (fun j ->
        get_tuple_id i j, Myformat.sprintf "proj_%d_%d_tuple" i (j-1)))))
  @ ExtList.repeat ~from:2 (preinstantiated_tuple + 1) (fun i ->
    mk_tuple_id i, Myformat.sprintf "mk_tuple%d" i)

let coq_predefined =
  [
    fst_id, "fst";
    snd_id, "snd";
  ]

let get_tuple_ids =
  List.flatten
    (ExtList.repeat ~from:2 (preinstantiated_tuple + 1) (fun i ->
      ExtList.repeat ~from:1 (i+1) (fun j ->
        get_tuple_id i j, j)))

let add_symbol s n =
  env.name_map <- Misc.StringMap.add s n env.name_map

let add_binding x t =
  env.ty_map <- Name.M.add x t env.ty_map

let add_symbol_and_binding s x t =
  add_symbol s x;
  add_binding x t

let type_of_var v = Name.M.find v env.ty_map

let base_var s = Misc.StringMap.find s env.name_map
let var s = try base_var s with Not_found -> error (PreludeIncomplete s)

let type_of_id s = type_of_var (var s)

let var_and_type s =
  let v = var s in
  let t = type_of_var v in
  v, t

let equal x id =
  try
    let y = base_var id in
    Name.equal x y
  with Not_found -> false

let belongs_to var id_list = List.exists (equal var) id_list
let find var id_list = List.find (fun (a,_) -> equal var a) id_list

let is_infix x = belongs_to x infix_ids

let is_effect_var x = belongs_to x effect_ids
let is_get_tuple_var x =
  try Some (snd (find x get_tuple_ids))
  with Not_found -> None

let build_map list =
  let map = ref None in
  fun () ->
    match !map with
    | Some x -> x
    | None ->
        let r =
          List.fold_left (fun acc (id,s) ->
            try Name.M.add (var id) s acc
            with _ -> acc) Name.M.empty list in
        map := Some r; r

let pangoline_map = build_map pangoline_predefined
let coq_map = build_map coq_predefined
