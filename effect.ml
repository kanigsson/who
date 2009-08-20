open Vars

exception IncompatibleSubst
module RB = RVar.BSet
module EB = EffVar.BSet
type t = RB.t * EB.t

let empty = RB.empty, EB.empty
let is_empty (rs,es) = RB.is_empty rs && EB.is_empty es
let esingleton e = RB.empty, EB.singleton e
let rsingleton r = RB.singleton r, EB.empty

let emem e (_,es) = EB.mem e es
let rmem r (rs,_) = RB.mem r rs

let union (rs1, es1) (rs2,es2) =
  RB.union rs1 rs2, EB.union es1 es2

let intersection (rs1, es1) (rs2,es2) =
  RB.intersection rs1 rs2, EB.intersection es1 es2

let free_rvars (rs,_) =
  RB.fold RVar.S.add rs RVar.S.empty

let are_disjoint (rs1,es1) (rs2,es2) = 
  RB.are_disjoint rs1 rs2 && EB.are_disjoint es1 es2

let disjoint_union e1 e2 =
  if are_disjoint e1 e2 then union e1 e2
  else raise IncompatibleSubst

let refresh s (rs,es) = 
  RB.map (RVar.refresh s) rs, EB.map (EffVar.refresh s) es

let rec compare (rs1,es1) (rs2,es2) = 
  let c = RB.compare rs1 rs2 in
  if c = 0 then EB.compare es1 es2 else c

let equal a b = compare a b = 0

let radd r (rs,es) = RB.add r rs, es
let eadd e (rs,es) = rs, EB.add e es

let fold f1 f2 (rs,es) acc = RB.fold f1 rs (EB.fold f2 es acc)
let efold f (_,es) acc = EB.fold f es acc
let rfold f (rs,_) acc = RB.fold f rs acc

let canon (rs,es) = RB.canon rs, EB.canon es
let effsubst ev eff (rs,es) =
  EB.fold 
    (fun e acc ->
      let ns = if EffVar.equal e ev then eff else esingleton e in
      disjoint_union ns acc) es (rs,EB.empty) 

let rsubst r nr ((rs,es) as t) = 
  if RB.mem r rs then
    if RB.mem nr rs then raise IncompatibleSubst
    else RB.add nr (RB.remove r rs), es
  else t

open Myformat
let print fmt (rs,es) = 
  if RB.is_empty rs then
    EB.print comma fmt es
  else begin
    RB.print comma fmt rs;
    if EB.is_empty es then ()
    else begin
      comma fmt ();
      EB.print comma fmt es
    end
  end

let print fmt x = fprintf fmt "{%a}" print x

let print_list = print_list semi print

let from_sets rs es = rs,es
let to_sets x = x

let explode e = 
  if is_empty e then [empty]
  else
    fold (fun r acc -> rsingleton r :: acc) 
         (fun e acc -> esingleton e :: acc)
         e []

let is_subset eff1 eff2 = 
  try 
    fold 
      (fun x () -> if rmem x eff2 then () else raise Not_found)
      (fun x () -> if emem x eff2 then () else raise Not_found)
      eff1 (); true
  with Not_found -> false

let minus acc y =
  fold
    (fun r (rs,es) -> RB.remove r rs, es)
    (fun e (rs,es) -> rs, EB.remove e es)
    y acc

let rremove r eff = minus eff (rsingleton r)
