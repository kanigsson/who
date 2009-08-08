open Vars
module SM = Misc.StringMap
module VM = Var.FreeMap
open Unify

let predefined = 
  [ "beq_z", eqz_var ]

let infer_env = 
  let nv = new_ty 1 in
  SM.add "beq_z" (0, arrow nv (arrow nv (const Const.TBool))) SM.empty

let intern_map = 
  List.fold_left (fun acc (s,v) -> SM.add s v acc) SM.empty predefined
