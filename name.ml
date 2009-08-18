module type NAME =
sig
  (** the module of Names. Names can be constructed from strings, but names with
   * the same underlying string are not necessarily equal (and aren't if
   * both constructed using [from_string]). *)
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val new_name : t -> t
  val new_anon : unit -> t
  val to_string : t -> string
  val from_string : string -> t
  val print : t Myformat.fmt
  val print_list : t list Myformat.fmt

  module M : Map.S with type key = t
  module S : Set.S with type elt = t

  val print_set : S.t Myformat.fmt
end

module Name =
struct
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
  module CMP = struct
    type t = t'
    let compare = compare
  end
  module M = Map.Make(CMP)
  module S = Set.Make(CMP)

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
    [ ]

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
  let print_set fmt s = 
    S.iter (fun x -> print fmt x ; space fmt ()) s

end

