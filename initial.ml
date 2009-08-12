module SM = Misc.StringMap

(*
module Infer = struct
  open Unify
  let infer_env = 
    let nv = new_ty () in
    SM.add "beq_z" (0, arrow nv (arrow nv (const Const.TBool))) SM.empty
end

let infer_env = Infer.infer_env
*)

open Ty
let typing_env = 
  let a = "a" in
  let va = var a in
  let r = "r" in
  SM.add "beq_z" (([a],[]), arrow va (arrow va (const Const.TBool)))
  (SM.add "!" (([a],[r]), arrow (ref_ r va) va) SM.empty)
