module SS = Misc.SS

type t = SS.t * SS.t * SS.t

let empty = SS.empty, SS.empty, SS.empty

exception CapError

let is_empty (r,e,c) = SS.is_empty r && SS.is_empty e && SS.is_empty c
let are_disjoint s1 s2 = SS.is_empty (SS.inter s1 s2)
let union (r1,e1,c1) (r2,e2,c2) = 
  if are_disjoint c1 c2 then
    SS.union r1 r2, SS.union e1 e2, SS.union c1 c2
  else raise CapError

let rsingleton r = SS.add r SS.empty, SS.empty, SS.empty
let esingleton e = SS.empty, SS.add e SS.empty, SS.empty

let radd rv (r,e,c) = SS.add rv r, e, c
let eadd ev (r,e,c) = r, SS.add ev e, c

let cadd r (r,e,c) = r,e,SS.add r c

open Myformat
let print fmt (r,e,c) = 
  if SS.is_empty c then fprintf fmt "{%a|%a}" print_set r print_set e
  else fprintf fmt "{%a|%a|%a}" print_set r print_set e print_set c

let print_list sep fmt l = print_list sep print fmt l

let smap f x = 
  SS.fold (fun x acc -> SS.add (f x) acc) x SS.empty

let rmap f (r,e,c) = smap f r, e, smap f c

let from_cap_list l = SS.empty,SS.empty, 
  List.fold_left (fun acc x -> SS.add x acc) SS.empty l

let lsubst el effl (rt,et,c) =
  let map = Misc.build_string_map el effl in
  let (nrt,ne,nc) = 
    SS.fold (fun ev acc -> 
      try union acc (Misc.StringMap.find ev map) with Not_found -> eadd ev acc)
      et empty in
  SS.union rt nrt, ne, SS.union c nc

let equal =
  let elts = SS.elements in
  fun (r1,e1,c1) (r2,e2, c2) ->
    elts r1 = elts r2 && elts e1 = elts e2 && c1 = c2

let rremove l (r,e,c) = 
  let f = SS.filter (fun x -> not (List.mem x l)) in
  f r, e, f c
