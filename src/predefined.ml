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

module Identifier = struct
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

  let fst_id = "fst"
  let snd_id = "snd"

  let plus_id = "+"
  let minus_id = "-"

  let combine_id = "combine"
  let restrict_id = "restrict"
  let get_id = "!!"
  let store_id = ":="


  let bool_id = "bool"
  let btrue_id = "true"
  let bfalse_id = "false"

  let unit_id = "unit"
  let void_id = "tt"

  let mk_tuple_id n = "mk_" ^ string_of_int n ^ "tuple"
  let get_tuple_id i j =
    "get_" ^ string_of_int i ^ "_" ^ string_of_int j ^ "_tuple"

  let unsafe_equal v id = 
    Name.unsafe_to_string v = id

end

module Logic = struct

  open Identifier

  let ty_map : (Ty.Generalize.t * Ty.t) Name.M.t ref = ref Name.M.empty
  let name_map : Name.t Misc.StringMap.t ref = ref Misc.StringMap.empty
  let pangoline_map : string Name.M.t ref = ref Name.M.empty

  let pangoline_predefined =
    [
      impl_id, "=>" ;
      not_id, "not" ;
      and_id, "and" ;
      or_id, "or" ;
      fst_id, "proj_2_0_tuple" ;
      snd_id, "proj_2_1_tuple" ;
    ]

  let init m = 
    ty_map := m;
    name_map := 
      Name.M.fold (fun x _ acc -> 
        Misc.StringMap.add (Name.unsafe_to_string x) x acc) m 
        Misc.StringMap.empty;
    pangoline_map :=
      List.fold_left (fun acc (id,pid) -> 
        Name.M.add (Misc.StringMap.find id !name_map) pid acc) Name.M.empty
        pangoline_predefined

  let type_of_var v = Name.M.find v !ty_map
  
  let var s = 
    try Misc.StringMap.find s !name_map
    with Not_found -> failwith s
  let type_of_id s = type_of_var (var s)

  let var_and_type s = 
    let v = var s in
    let t = type_of_var v in
    v, t

  let get_pangoline_id x = 
    Name.M.find x !pangoline_map

  let equal x id = 
    let y = var id in
    Name.equal x y

  let belongs_to var id_list = List.exists (equal var) id_list

end
