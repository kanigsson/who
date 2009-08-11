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
  SM.add "beq_z" (["a"], arrow (var "a") (arrow (var "a") (const Const.TBool)))
    SM.empty
