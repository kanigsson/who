open Name
module Var = Name
module TyVar = Name
module RVar = Name
module EffVar = Name

let h = Hashtbl.create 17

let add_var s x = Hashtbl.add h s x
let get_predef_var s = 
  try Hashtbl.find h s
  with Not_found -> failwith ("predef_var: " ^ s)
