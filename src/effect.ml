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

module S = Name.S
type t = S.t * S.t

let empty = S.empty, S.empty
let is_empty (r,e) = S.is_empty r && S.is_empty e
let no_effvar (_,e) = S.is_empty e

let are_disjoint s1 s2 = S.is_empty (S.inter s1 s2)
let union (r1,e1) (r2,e2) = S.union r1 r2, S.union e1 e2
let union3 a b c = union a (union b c)

let rsingleton r = S.add r S.empty, S.empty
let esingleton e = S.empty, S.add e S.empty

let rremove (r,e) l =
  S.filter (fun x -> not (List.mem x l)) r, e

let eremove (r,e) ev = r, S.remove ev e


let radd (r,e) rv = S.add rv r, e
let eadd (r,e) ev = r, S.add ev e

let rmem (rs,_) r = S.mem r rs
let emem (_,es) e = S.mem e es

let from_lists rl el = Name.list_to_set rl, Name.list_to_set el
let from_u_effect rl es = Name.list_to_set rl, es

let to_lists, to_rlist, to_elist =
  let list_from_set l = S.fold (fun x acc -> x ::acc) l [] in
  (fun (r,e) -> list_from_set r, list_from_set e),
  (fun (r,_) -> list_from_set r),
  (fun (_,e) -> list_from_set e)

let to_u_effect ((_,e) as eff) = to_rlist eff, e

let is_esingleton (rl,el) =  S.is_empty rl && S.cardinal el = 1
let e_choose (_,el) = S.choose el

let rsmap f x =
  S.fold (fun x acc -> S.add (f x) acc) x S.empty

let rmap f (r,e) = rsmap f r, e

let eiter f (_,e) = S.iter f e
let rfold f acc (r,_) = S.fold f r acc
let efold f acc (_,e) = S.fold f e acc

let build_effvar_map el effl =
  List.fold_left2 (fun acc k v -> Name.M.add k v acc) Name.M.empty el effl

let lsubst el effl (rt,et) =
  let map = build_effvar_map el effl in
  let (nrt,ne) =
    S.fold (fun ev acc ->
      try union acc (Name.M.find ev map) with Not_found -> eadd acc ev)
      et empty in
  S.union rt nrt, ne

let s_equal a b =
  ExtList.equal Name.equal (S.elements a) (S.elements b)
let equal (r1,e1) (r2, e2) = s_equal r1 r2 && s_equal e1 e2

module Convert = struct
  module SS = Misc.StringSet

  open PrintTree

  let build_string_list env s =
    List.rev (S.fold (fun x acc -> Env.id env x :: acc) s [])

  let t env (r,e) = build_string_list env r, build_string_list env e
end

module Print = struct
  open PrintTree

  let nosep fmt e = Print.effect_no_sep fmt (Convert.t Env.empty e)
  let effect fmt e = Print.effect fmt (Convert.t Env.empty e)
  let list sep = Myformat.list sep effect
end

let print_nosep = Print.nosep
let print = Print.effect
let print_list = Print.list


let inter (r1,e1) (r2,e2) = S.inter r1 r2, S.inter e1 e2
let diff (r1,e1) (r2,e2) = S.diff r1 r2, S.diff e1 e2

let split d1 d2 =
  let d1 = diff d1 d2 and d2 = diff d2 d1 and d3 = inter d1 d2 in
  d1, d3, d2

let sub_effect (r1,e1) (r2,e2) = S.subset r1 r2 && S.subset e1 e2


