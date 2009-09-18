module S = Name.S
type t = S.t * S.t * S.t

let empty = S.empty, S.empty, S.empty

exception CapError

let is_empty (r,e,c) = S.is_empty r && S.is_empty e && S.is_empty c
let are_disjoint s1 s2 = S.is_empty (S.inter s1 s2)
let union (r1,e1,c1) (r2,e2,c2) = 
  if are_disjoint c1 c2 then
    S.union r1 r2, S.union e1 e2, S.union c1 c2
  else raise CapError

let rsingleton r = S.add r S.empty, S.empty, S.empty
let esingleton e = S.empty, S.add e S.empty, S.empty

let radd rv (r,e,c) = S.add rv r, e, c
let eadd ev (r,e,c) = r, S.add ev e, c

let rmem r (rs,_,_) = S.mem r rs

let cadd r (rs,e,c) = rs,e,S.add r c

open Myformat
let print fmt (r,e,c) = 
  if S.is_empty c then 
    fprintf fmt "{%a|%a}" Name.print_set r Name.print_set e
  else 
    fprintf fmt "{%a|%a|%a}" Name.print_set r Name.print_set e Name.print_set c

let print_list sep fmt l = print_list sep print fmt l

let rsmap f x = 
  S.fold (fun x acc -> S.add (f x) acc) x S.empty

let rmap f (r,e,c) = rsmap f r, e, rsmap f c

let from_cap_list l = S.empty,S.empty, 
  List.fold_left (fun acc x -> S.add x acc) S.empty l

let build_effvar_map el effl =
  List.fold_left2 (fun acc k v -> Name.M.add k v acc) Name.M.empty el effl

let lsubst el effl (rt,et,c) =
  let map = build_effvar_map el effl in
  let (nrt,ne,nc) = 
    S.fold (fun ev acc -> 
      try union acc (Name.M.find ev map) with Not_found -> eadd ev acc)
      et empty in
  S.union rt nrt, ne, S.union c nc

let equal = 
  let cmp a b = Misc.list_equal Name.compare (S.elements a) (S.elements b) in
  fun (r1,e1,c1) (r2, e2, c2) -> cmp r1 r2 && cmp e1 e2 && cmp c1 c2

let sequal = 
  let cmp a b = Misc.list_equal Name.compare (S.elements a) (S.elements b) in
  fun (r1,e1,_) (r2,e2, _) -> cmp r1 r2 && cmp e1 e2

let rremove l (r,e,c) = 
  let f = S.filter (fun x -> not (List.mem x l)) in
  f r, e, f c

let clean (r,e,_) = r,e,S.empty
