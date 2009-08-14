open Vars

type ('a,'b,'c) t = 'a * 'b * 'c 

open Format
let print pra prb prc fmt (tl,rl,el) =
  fprintf fmt "[%a|%a|%a]" pra tl prb rl prc el
