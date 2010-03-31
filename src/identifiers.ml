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

let equal_id = "="
let empty_id = "empty"
let not_id = "~"
let leb_id = "<<="
let ltb_id = "<<"
let gtb_id = ">>"
let geb_id = ">>="
let eqb_id = "=="
let neqb_id = "!="
let andb_id = "band"
let orb_id = "bor"
let le_id = "<="
let lt_id = "<"
let ge_id = ">="
let gt_id = ">"
let neq_id = "<>"
let and_id = "/\\"
let or_id = "\\/"
let impl_id = "->"

let plus_id = "+"
let minus_id = "-"

let combine_id = "combine"
let restrict_id = "restrict"
let get_id = "!!"
let store_id = ":="


let refget_id = "ref_get"
let btrue_id = "true"
let bfalse_id = "false"

let void_id = "tt"

let mk_tuple_id n = "mk_" ^ string_of_int n ^ "tuple"
let get_tuple_id i j =
  "get_" ^ string_of_int i ^ "_" ^ string_of_int j ^ "_tuple"

let fst_id = get_tuple_id 2 1
let snd_id = get_tuple_id 2 2

let unsafe_equal v id =
  Name.unsafe_to_string v = id

let infix_ids =
  [
    equal_id; leb_id ; ltb_id; gtb_id; geb_id; eqb_id; neqb_id; le_id; lt_id;
    ge_id; gt_id; neq_id; and_id; or_id; andb_id; orb_id; impl_id; plus_id;
    minus_id; store_id;
  ]

let effect_ids =
  [
    combine_id; restrict_id; get_id; empty_id
  ]

let is_infix_id id = List.exists (fun x -> x = id) infix_ids

