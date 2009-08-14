open Vars
type t = tvar list * rvar list * effvar list

let empty = [],[],[]
let is_empty = function
  | [],[],[] -> true
  | _ -> false

open Format
let print fmt ((tl,rl,el) as g) = 
  if is_empty g then ()
  else fprintf fmt "[%a|%a|%a]" tvarlist tl rvarlist rl effvarlist el

