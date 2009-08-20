type t = { name : string option ; n : int }
let compare a b = Pervasives.compare a.n b.n
let equal a b = compare a b = 0

let new_name =
  let x = ref 0 in
  function n -> incr x; {n with n = !x}
let new_anon () = new_name { name = None; n = 0 }
let from_string s = new_name {name = Some s; n = 0}
let to_string n = 
  match n.name with
  | Some s -> s
  | None -> "anon"

type t' = t


(* Clean name generation *)
(* map which gives the next index of a new variable *)
let name_map = Hashtbl.create 47

(* map which gives the current name of a variable *)
let current_name_map = Hashtbl.create 47

let fresh_string s = 
  try
    let i = Hashtbl.find name_map s in
    let s = s ^ (string_of_int !i) in
    incr i; s
  with Not_found ->
    let x = ref 1 in
    Hashtbl.add name_map s x;
    s

let to_string n = fresh_string (to_string n)

let reserved_names = 
  [ "Definition"; "for"; "end"; "Lemma"; "Parameter"; ]

let reset () = 
  Hashtbl.clear name_map;
  List.iter (fun s -> ignore (fresh_string s)) reserved_names

let get_cur_name x = 
  try Hashtbl.find current_name_map x
  with Not_found ->
    let s = to_string x in
    Hashtbl.add current_name_map x s;
    s

open Myformat
let print fmt x = fprintf fmt "%s" (get_cur_name x)
let print_list fmt x = print_list space print fmt x

module CMP = struct
  type t = t'
  let compare = compare
  let equal = equal
  let print = print
end
module M = Map.Make(CMP)
module S = Set.Make(CMP)
module BMap = ListMap.Make(CMP)
module BSet = ListSet.Make(CMP)

let print_set fmt s = 
  S.iter (fun x -> print fmt x ; space fmt ()) s


let h = Hashtbl.create 17

let add_var s x = Hashtbl.add h s x
let get_predef_var s = 
  try Hashtbl.find h s
  with Not_found -> failwith ("predef_var: " ^ s)
