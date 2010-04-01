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

type t = { name : string option ; n : int }
type subst = (t * t) list
type 'a bind = subst * t * 'a
type 'a listbind = subst * t list * 'a

let compare a b = Pervasives.compare a.n b.n
let equal a b = compare a b = 0
let hash a = a.n

let default_string = "anon"
let new_name =
  let x = ref 0 in
  function n -> incr x; {n with n = !x}
let new_anon () = new_name { name = None; n = 0 }
let from_string s = new_name {name = Some s; n = 0}
let unsafe_to_string n =
  match n.name with
  | Some s -> s
  | None -> default_string

let refresh' (y,t) x = if equal x y then t else x
let refresh = List.fold_right refresh'
let refresh_bind s (s',v,t) = List.append s s', v, t
let refresh_listbind s (s',v,t) = List.append s s', v, t

let open_with f nv (s,v,t) =
  let t = f [v,nv] t in
  f s t

let open_bind f ((_,v,_) as k) =
  let nv = new_name v in
  let t = open_with f nv k in
  nv, t

let close_bind nv t = ([],nv,t)

let sopen f (s,v,t) =
  let t = f s t in
  v, t

let list_open_with f nvl (s,vl,t) =
  let subst = List.combine vl nvl in
  let t = f subst t in
  f s t

let open_listbind f ((_,vl,_) as k) =
  let nvl = List.map new_name vl in
  let t = list_open_with f nvl k in
  nvl,t

let close_listbind nvl t = ([],nvl,t)

let append n s = from_string (unsafe_to_string n ^ s)

(* Clean name generation *)
(* map which gives the next index of a new variable *)
let name_map = Hashtbl.create 47

let strip_numbers s =
  let rec aux n =
    if n <= 0 then 0
    else
      match s.[n-1] with
      | '0'..'9' -> aux (n-1)
      | _ -> n in
  let n = aux (String.length s) in
  if n = 0 then default_string else String.sub s 0 n

let fresh_string_env env name =
  let s = strip_numbers name in
  try
    let i = Misc.StringMap.find s env in
    let s' = s ^ (string_of_int i) in
    Misc.StringMap.add s (i+1) env, s'
  with Not_found -> Misc.StringMap.add s 1 env, s


let name_map = ref Misc.StringMap.empty


let fresh_string x =
  let env, s = fresh_string_env !name_map x in
  name_map := env; s

let to_string n = fresh_string (unsafe_to_string n)

let reserved_names =
  [ "Definition"; "for"; "end"; "Lemma"; "Parameter"; ]

let reset () =
  name_map := Misc.StringMap.empty;
  List.iter (fun s -> ignore (fresh_string s)) reserved_names

let print fmt x = Format.pp_print_string fmt (unsafe_to_string x)

module CMP = struct
  type t' = t
  type t = t'
  let compare = compare
  let equal = equal
  let print = print
  let hash x = Hashtbl.hash x.n
end
module M = Map.Make(CMP)
module S = Set.Make(CMP)
module H = Hashtbl.Make(CMP)

let list_to_set l = List.fold_left (fun acc x -> S.add x acc) S.empty l
let set_to_list s = S.fold (fun x acc -> x::acc) s []
let remove_list_from_set l s = List.fold_left (fun acc x -> S.remove x acc) s l

let get_cur_name =
  let current_name_map = H.create 47 in
  fun x ->
    try H.find current_name_map x
    with Not_found ->
      let s = to_string x in
      H.add current_name_map x s;
      s

open Myformat
let print fmt x = string fmt (get_cur_name x)
let print_list fmt x = list space print fmt x

let print_set fmt s =
  S.iter (fun x -> print fmt x ; space fmt ()) s

let hash_set s =
  S.fold (fun x acc -> Hash.combine (hash x) acc) s 2

module Env = struct
  type name = t
  type t =
    { names : string M.t;
      gen : int Misc.StringMap.t ;
      predefined : string M.t;
    }

  let empty predefined =
    { names = M.empty;
      gen = Misc.StringMap.empty ;
      predefined = predefined
    }

  let id env x =
    try M.find x env.predefined
    with Not_found ->
      try M.find x env.names
      with Not_found -> get_cur_name x

  let add_id env x =
    (* ignore predefined names *)
    if M.mem x env.predefined then begin
      env
    end else begin
      let gen, s = fresh_string_env env.gen (unsafe_to_string x) in
      { env with names = M.add x s env.names; gen = gen }
    end

  let add_id_list = List.fold_left add_id

  let is_predefined env n = M.mem n env.predefined
end

