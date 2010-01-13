module S = Name.S
type t = S.t * S.t

let empty = S.empty, S.empty
let is_empty (r,e) = S.is_empty r && S.is_empty e
let no_effvar (_,e) = S.is_empty e

let are_disjoint s1 s2 = S.is_empty (S.inter s1 s2)
let union (r1,e1) (r2,e2) = S.union r1 r2, S.union e1 e2

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

let to_lists, to_rlist, to_elist =
  let list_from_set l = S.fold (fun x acc -> x ::acc) l [] in
  (fun (r,e) -> list_from_set r, list_from_set e),
  (fun (r,_) -> list_from_set r),
  (fun (_,e) -> list_from_set e)

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

let equal = 
  let cmp a b = Misc.list_equal Name.compare (S.elements a) (S.elements b) in
  fun (r1,e1) (r2, e2) -> cmp r1 r2 && cmp e1 e2

open Myformat
let print_set fmt s = 
  S.iter (fun x -> fprintf fmt "'%a" Name.print x ; space fmt ()) s

let print_nosep fmt (r,e) = 
    fprintf fmt "%a %a" Name.print_set r print_set e
let print fmt e = fprintf fmt "{%a}" print_nosep e


let print_list sep fmt l = print_list sep print fmt l

let inter (r1,e1) (r2,e2) = S.inter r1 r2, S.inter e1 e2
let diff (r1,e1) (r2,e2) = S.diff r1 r2, S.diff e1 e2

let split d1 d2 = 
  let d1 = diff d1 d2 and d2 = diff d2 d1 and d3 = inter d1 d2 in
  d1, d3, d2

let sub_effect (r1,e1) (r2,e2) = S.subset r1 r2 && S.subset e1 e2


