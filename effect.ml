module SS = Misc.SS

type t = SS.t * SS.t

let empty = SS.empty, SS.empty
let union (r1,e1) (r2,e2) = SS.union r1 r2, SS.union e1 e2

open Myformat
let print fmt (r,e) = fprintf fmt "{%a|%a}" print_set r print_set e
let print_list sep fmt l = print_list sep print fmt l

let map f x = 
  SS.fold (fun x acc -> SS.add (f x) acc) x SS.empty

let subst e eff ((rt,et) as t) = 
  if SS.mem e et then union eff (rt, SS.remove e et) else t

let equal =
  let elts = SS.elements in
  fun (r1,e1) (r2,e2) ->
    elts r1 = elts r2 && elts e1 = elts e2

  
