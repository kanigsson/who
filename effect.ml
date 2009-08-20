open Names
module RS = RVar.S
module ES = EffVar.S
type t = RS.t * ES.t * RS.t

let empty = RS.empty, ES.empty, RS.empty

exception CapError

let is_empty (r,e,c) = RS.is_empty r && ES.is_empty e && RS.is_empty c
let are_disjoint s1 s2 = RS.is_empty (RS.inter s1 s2)
let union (r1,e1,c1) (r2,e2,c2) = 
  if are_disjoint c1 c2 then
    RS.union r1 r2, ES.union e1 e2, RS.union c1 c2
  else raise CapError

let rsingleton r = RS.add r RS.empty, ES.empty, RS.empty
let esingleton e = RS.empty, ES.add e ES.empty, RS.empty

let radd rv (r,e,c) = RS.add rv r, e, c
let eadd ev (r,e,c) = r, ES.add ev e, c

let cadd r (r,e,c) = r,e,RS.add r c

open Myformat
let print fmt (r,e,c) = 
  if RS.is_empty c then 
    fprintf fmt "{%a|%a}" RVar.print_set r EffVar.print_set e
  else 
    fprintf fmt "{%a|%a|%a}" RVar.print_set r EffVar.print_set e RVar.print_set c

let print_list sep fmt l = print_list sep print fmt l

let rsmap f x = 
  RS.fold (fun x acc -> RS.add (f x) acc) x RS.empty

let rmap f (r,e,c) = rsmap f r, e, rsmap f c

let from_cap_list l = RS.empty,ES.empty, 
  List.fold_left (fun acc x -> RS.add x acc) RS.empty l

let build_effvar_map el effl =
  List.fold_left2 (fun acc k v -> EffVar.M.add k v acc) EffVar.M.empty el effl

let lsubst el effl (rt,et,c) =
  let map = build_effvar_map el effl in
  let (nrt,ne,nc) = 
    ES.fold (fun ev acc -> 
      try union acc (EffVar.M.find ev map) with Not_found -> eadd ev acc)
      et empty in
  RS.union rt nrt, ne, RS.union c nc

let equal =
  let relts = RS.elements in
  let eelts = ES.elements in
  fun (r1,e1,c1) (r2,e2, c2) ->
    Misc.list_equal RVar.compare (relts r1) (relts r2) &&
    Misc.list_equal RVar.compare (relts c1) (relts c2) &&
    Misc.list_equal EffVar.compare (eelts e1) (eelts e1)

let rremove l (r,e,c) = 
  let f = RS.filter (fun x -> not (List.mem x l)) in
  f r, e, f c
