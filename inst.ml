open Vars

type ('a,'b,'c) t = 'a list * 'b list * 'c list 

let empty = [],[],[]
let is_empty x = x = empty

open Myformat
let prl pr = print_list comma pr
let print pra prb prc fmt ((tl,rl,el) as g) =
  if is_empty g then () else
    fprintf fmt "[%a|%a|%a]" (prl pra) tl (prl prb) rl (prl prc) el
