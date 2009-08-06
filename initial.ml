open Vars
module SM = Misc.StringMap

let predefined = 
  [ "beq_z", eqz_var ]

let intern_map = 
  List.fold_left (fun acc (s,v) -> SM.add s v acc) SM.empty predefined
  
