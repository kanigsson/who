type var = string
type tvar = string
type rvar = string
type effvar = string

open Myformat
let var = pp_print_string
let tvar = pp_print_string
let rvar = pp_print_string
let effvar = pp_print_string

let varlist = print_list space var
let tvarlist = print_list space var
let rvarlist = print_list space var
let effvarlist = print_list space var
