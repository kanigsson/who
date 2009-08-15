open Vars

type ('a,'b,'c) t = 'a list * 'b list * 'c list 

let empty = [],[],[]
let is_empty x = x = empty

open Myformat
let prl pr = print_list comma pr
let print pra prb prc fmt ((tl,rl,el) as g) =
  if is_empty g then () else
    fprintf fmt "[%a|%a|%a]" (prl pra) tl (prl prb) rl (prl prc) el

let map fa fb fc (tl,rl,el) =
  List.map fa tl, List.map fb rl, List.map fc el

let iter2 fa fb fc (tl1,rl1,el1) (tl2,rl2,el2) =
  List.iter2 fa tl1 tl2;
  List.iter2 fb rl1 rl2;
  List.iter2 fc el1 el2;
