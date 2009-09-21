type t = 
  | Int of Big_int.big_int
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

open Myformat
let print fmt = function
  | Int b -> pp_print_string fmt (Big_int.string_of_big_int b)
  | Void -> pp_print_string fmt "tt"
  | Btrue -> pp_print_string fmt "true"
  | Bfalse -> pp_print_string fmt "false"
  | Ptrue -> pp_print_string fmt "True"
  | Pfalse -> pp_print_string fmt "False"

let print_ty fmt = function
  | TBool -> pp_print_string fmt "bool"
  | TInt -> pp_print_string fmt "int"
  | TUnit -> pp_print_string fmt "unit"
  | TProp -> pp_print_string fmt "Prop"

let quant fmt = function
  | `FA -> pp_print_string fmt "forall"
  | `EX -> pp_print_string fmt "exists"
  | `LAM -> pp_print_string fmt "λ"

let quantsep fmt = function
  | `FA | `EX -> pp_print_string fmt "."
  | `LAM -> pp_print_string fmt "->"

let compare a b = 
  match a,b with
  | Int i1, Int i2 -> Big_int.compare_big_int i1 i2
  | _, _ -> Pervasives.compare a b
