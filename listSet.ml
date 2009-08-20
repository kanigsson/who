module Make (O : MySet.CanonType) =

struct
  type elt = O.t
  type t = O.t list

  let empty = []
  let is_empty x = x = []

  let singleton x = [x]

  let rec mem x = function
    | [] -> false
    | y::r -> if O.equal x y then true else mem x r

  let add x l = if mem x l then l else x::l

  let rec remove x = function
    | [] -> []
    | y::r -> if O.equal x y then r else y::(remove x r)

  let union l1 l2 = List.fold_left (fun acc x -> add x acc) l1 l2

  let intersection l1 l2 =
    List.filter (fun x -> mem x l2) l1

  let are_disjoint l1 l2 =
    let rec aux = function
      | [] -> true
      | y::r -> if mem y l2 then false else aux r
    in
    aux l1

  let iter f l = List.iter f l

  let fold f = List.fold_right f

  let map f l = fold (fun e acc -> add (f e) acc) l empty

  let canon l = List.sort O.compare l
  
  let compare l1 l2 = 
    let l1 = canon l1 and l2 = canon l2 in
    let rec aux l1 l2 =
      match l1, l2 with
        | [], [] -> 0
        | [], _  -> 1
        | _, [] -> -1
        | (x::xs), (y::ys) -> 
            let c = O.compare x y in
              if c = 0 then aux xs ys else c
    in
    aux l1 l2

  open Myformat
  let print sep fmt l = 
    let l = canon l in
    print_list sep O.print fmt l

end
