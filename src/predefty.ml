let bool_var = Name.from_string "bool"
let unit_var = Name.from_string "unit"

module SM = Misc.StringMap

let allvars = [ bool_var ; unit_var ]
let map =
  List.fold_left (fun acc x ->
    SM.add (Name.unsafe_to_string x) x acc) SM.empty allvars
