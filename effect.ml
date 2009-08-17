module SS = Misc.SS

type t = SS.t * SS.t

let empty = SS.empty, SS.empty

let is_empty (r,e) = SS.is_empty r && SS.is_empty e
let union (r1,e1) (r2,e2) = SS.union r1 r2, SS.union e1 e2

let rsingleton r = SS.add r SS.empty, SS.empty
let esingleton e = SS.empty, SS.add e SS.empty

let radd rv (r,e) = SS.add rv r, e
let eadd ev (r,e) = r, SS.add ev e

open Myformat
let print fmt (r,e) = fprintf fmt "{%a|%a}" print_set r print_set e
let print_list sep fmt l = print_list sep print fmt l

let map f x = 
  SS.fold (fun x acc -> SS.add (f x) acc) x SS.empty

let lsubst el effl (rt,et) =
  let map = Misc.build_string_map el effl in
  let (nrt,ne) = 
    SS.fold (fun ev acc -> 
      try union acc (Misc.StringMap.find ev map) with Not_found -> eadd ev acc)
      et empty in
  SS.union rt nrt, ne

let equal =
  let elts = SS.elements in
  fun (r1,e1) (r2,e2) ->
    elts r1 = elts r2 && elts e1 = elts e2

  
