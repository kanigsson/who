module Make (O : MySet.CanonType) =
struct
  type key = O.t
  type 'a t = (O.t * 'a) list

  let empty = []
  let is_empty x = x = []
  let domain x = List.map fst x

  let find elem l =
    let rec aux = function
      | [] -> raise Not_found
      | (v,x)::r ->
          if O.equal v elem  then x
          else aux r
    in
    aux l
  let sort l = List.sort (fun a b -> O.compare (fst a) (fst b)) l
  let canon = sort

  let rec mem k = function
    | [] -> false
    | (y,_)::r -> if O.equal k y then true else mem k r

  let add k v l = 
    let rec aux = function
      | [] -> [k,v]
      | ((y,_) as p) :: r -> 
          if O.equal k y then (y,v)::r
          else p::(aux r)
    in
    aux l
    
  let map f l = 
    List.map (fun (k,v) -> k, f v) l

  let fold f = List.fold_right (fun (k,v) -> f k v)

  let fold_up f l acc = 
    List.fold_left (fun acc (k,v) -> f k v acc) acc l

  let rec compose l1 l2 = 
    let l1 = canon l1 and l2 = canon l2 in
    match l1,l2 with
    | [],_ -> l2
    | _,[] -> l1
    | ((el1,_) as h1)::r1, ((el2,_) as h2)::r2 ->
        let c = O.compare el1 el2 in
        if c > 0 then h1::compose r1 l2
        else if c < 0 then h2::compose l1 r2
        else h2::compose r1 r2

  let iter f = List.iter (fun (a,b) -> f a b) 

  let restrict l1 l2 = 
    List.fold_right 
    (fun ((x,_) as p) acc -> if List.mem x l2 then p :: acc else acc)
    l1 empty
    

(*
  let rec restrict l1 l2 = 
    let l1 = sort l1 and l2 = List.sort O.compare l2 in
    match l1,l2 with
    | _, []  | [],_ ->  []
    | ((k1,el1) as hd1)::tl, k2::tl2 ->
        let c = O.compare k1 k2 in
        if c = 0 then hd1::(restrict tl tl2)
        else if c < 0 then restrict l1 tl2
        else restrict tl l2
*)

  open Myformat
  let print sep prval = 
    let prelem fmt (k,v) = Format.fprintf fmt "%a = %a" O.print k prval v in
    print_list sep prelem 
end
