open Vars
module SM = Misc.StringMap
module VM = Var.FreeMap
open Unify

(*
let predefined = 
  [ "beq_z", eqz_var ]

let infer_env = 
  let nv = new_ty 1 in
  VM.add eqz_var (0, arrow nv (arrow nv (const Ty.Bool))) VM.empty

let intern_map = 
  List.fold_left (fun acc (s,v) -> SM.add s v acc) SM.empty predefined
  
*)
