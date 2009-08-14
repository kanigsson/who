open Format

let lineno = ref 0
let newlinepos = ref 0

let pair_compare cmpa cmpb (a1,b1) (a2,b2) =
  let c = cmpa a1 a2 in
  if c = 0 then cmpb b1 b2 else c

let cnt =
  let x = ref 0 in
    fun () -> incr x ; !x

let rec list_compare cmp l1 l2 = 
  match l1,l2 with
  | [],[] -> 0
  | [],_ -> 1
  | _,[] -> -1
  | (h1::r1), (h2::r2) -> 
      let c = cmp h1 h2 in
      if c <> 0 then c
      else list_compare cmp r1 r2

let list_equal cmp l1 l2 =
  list_compare cmp l1 l2 = 0

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module SS = StringSet

let rec fold_down f acc n = 
  if n <= 0 then acc
  else fold_down f (f acc n) (n-1)

let id x = x

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

let fold_map f acc l = 
  let rec aux acc = function
    | [] -> []
    | x::xs ->
        let acc, x = f acc x in
        x :: aux acc xs
  in
  aux acc l
        
