open Vars

type ('a,'b,'c) t = 'a list * 'b list * 'c list 

let empty = [],[],[]

open Myformat
let prl pr = print_list comma pr
let print pra prb prc fmt (tl,rl,el) =
  fprintf fmt "[%a|%a|%a]" (prl pra) tl (prl prb) rl (prl prc) el
