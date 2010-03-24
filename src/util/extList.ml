type 'a t = 'a list
type 'a eq = 'a -> 'a -> bool

let rec list_compare cmp l1 l2 =
  match l1,l2 with
  | [],[] -> 0
  | [],_ -> 1
  | _,[] -> -1
  | (h1::r1), (h2::r2) ->
      let c = cmp h1 h2 in
      if c <> 0 then c
      else list_compare cmp r1 r2

let equal eq l1 l2 =
  list_compare (fun x y -> if eq x y then 0 else -1) l1 l2 = 0

let mem eq x l = List.exists (fun b -> eq x b) l

let contained eq l1 l2 =
  List.for_all (fun a -> mem eq a l2) l1

let equal_unsorted eq l1 l2 =
  contained eq l1 l2 && contained eq l2 l1

let union eq l1 l2 =
  List.fold_left
    (fun acc x -> if mem eq x acc then acc else x :: acc) l2 l1

let map_filter map filter l =
  let rec aux = function
  | [] -> []
  | x::xs ->
      let x = map x in
      let xs = aux xs in
      if filter x then x :: xs else xs
  in
  aux l

let fold_left_rev_map f acc l =
  List.fold_left
    (fun (acc,l) d ->
      let acc, d = f acc d in
      acc, d::l
    ) (acc,[]) l

let fold_map f init l =
  let rec flm acu l' = function
    | [] ->
        (acu, List.rev l')
    | x :: xs ->
        let (acu, y) = f acu x in
          flm acu (y :: l') xs
  in
    flm init [] l

let repeat ?(from=0) n f =
  let rec loop i accu =
    if i = n then List.rev accu
    else loop (i + 1) (f i :: accu)
  in
    loop from []
