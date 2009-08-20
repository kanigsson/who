type t = 
  | Int of int
  | Void
  | Btrue
  | Bfalse
  | Ptrue
  | Pfalse

type ty = 
  | TBool
  | TInt
  | TUnit
  | TProp

type fix = Infix | Prefix

let type_of_constant = function
  | Int _ -> TInt
  | Void -> TUnit
  | Btrue | Bfalse -> TBool
  | Ptrue | Pfalse -> TProp

open Format
let print fmt = function
  | Int i -> pp_print_int fmt i
  | Void -> pp_print_string fmt "()"
  | Btrue -> pp_print_string fmt "true"
  | Bfalse -> pp_print_string fmt "false"
  | Ptrue -> pp_print_string fmt "True"
  | Pfalse -> pp_print_string fmt "False"

let print_ty fmt = function
  | TBool -> pp_print_string fmt "bool"
  | TInt -> pp_print_string fmt "nat"
  | TUnit -> pp_print_string fmt "unit"
  | TProp -> pp_print_string fmt "prop"

let quant fmt = function
  | `FA -> pp_print_string fmt "forall"
  | `EX -> pp_print_string fmt "exists"
  | `LAM -> pp_print_string fmt "λ"

let quantsep fmt = function
  | `FA | `EX -> pp_print_string fmt "."
  | `LAM -> pp_print_string fmt "->"
