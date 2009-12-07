module S = Name.S
type t = S.t * S.t

let empty = S.empty, S.empty

exception CapError

let is_empty (r,e,c) = S.is_empty r && S.is_empty e
let are_disjoint s1 s2 = S.is_empty (S.inter s1 s2)
let union (r1,e1) (r2,e2) = S.union r1 r2, S.union e1 e2

let rsingleton r = S.add r S.empty, S.empty
let esingleton e = S.empty, S.add e S.empty

let radd rv (r,e) = S.add rv r, e
let eadd ev (r,e) = r, S.add ev e

let rmem r (rs,_) = S.mem r rs
let emem e (_,es) = S.mem e es

open Myformat
let print fmt (r,e) = 
    fprintf fmt "{%a|%a}" Name.print_set r Name.print_set e

let print_list sep fmt l = print_list sep print fmt l

let rsmap f x = 
  S.fold (fun x acc -> S.add (f x) acc) x S.empty

let rmap f (r,e) = rsmap f r, e

let rfold f acc (r,_) = S.fold f r acc
let efold f acc (_,e) = S.fold f e acc

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
  fun (r1,e1) (r2, e2) -> cmp r1 r2 && cmp e1 e2

let rremove l (r,e) = 
  S.filter (fun x -> not (List.mem x l)) r, e
