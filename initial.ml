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

module SS = Misc.SS
open Ty
let typing_env = 
  let a = "a" in
  let va = var a in
  let r = "r" in
  let se = SS.empty in
  let e = se, se in
  let re = SS.add r se, se in
  SM.add "beq_z" (([a],[],[]), arrow va (arrow va (const Const.TBool) e) e)
  (SM.add "!" (([a],[r],[]), arrow (ref_ r va) va re) SM.empty)
