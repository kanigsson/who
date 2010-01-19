type t = { name : string option ; n : int }
type subst = (t * t) list
type 'a bind = subst * t * 'a
type 'a listbind = subst * t list * 'a

let compare a b = Pervasives.compare a.n b.n
let equal a b = compare a b = 0

let new_name =
  let x = ref 0 in
  function n -> incr x; {n with n = !x}
let new_anon () = new_name { name = None; n = 0 }
let from_string s = new_name {name = Some s; n = 0}
let unsafe_to_string n = 
  match n.name with
  | Some s -> s
  | None -> "anon"

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

let to_string n = fresh_string (unsafe_to_string n)

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
  type t' = t
  type t = t'
  let compare = compare
  let equal = equal
  let print = print
end
module M = Map.Make(CMP)
module S = Set.Make(CMP)
let print_set fmt s = 
  S.iter (fun x -> print fmt x ; space fmt ()) s


let list_to_set l = List.fold_left (fun acc x -> S.add x acc) S.empty l
let set_to_list s = S.fold (fun x acc -> x::acc) s []
let remove_list_from_set l s = List.fold_left (fun acc x -> S.remove x acc) s l

