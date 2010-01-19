type t = 
  | Int of Big_int.big_int
  | Void
  | Ptrue
  | Pfalse

type ty = 
  | TInt
  | TUnit
  | TProp

type 'a isrec = 
  | LogicDef
  | NoRec
  | Rec of 'a

type fix = Infix | Prefix

let type_of_constant = function
  | Int _ -> TInt
  | Void -> TUnit
  | Ptrue | Pfalse -> TProp

type takeover = [`Coq | `Pangoline ] * choice
and choice = 
  | Include of string
  | TakeOver 
  | Predefined

open Myformat
let print kind fmt = function
  | Int b -> pp_print_string fmt (Big_int.string_of_big_int b)
  | Void -> 
      begin match kind with 
      | `Coq -> pp_print_string fmt "tt"
      | _ -> pp_print_string fmt "()"
      end
  | Ptrue -> pp_print_string fmt "True"
  | Pfalse -> pp_print_string fmt "False"

let funsep fmt kind = 
  match kind with
  | `Who | `Pangoline -> pp_print_string fmt "->"
  | `Coq -> pp_print_string fmt "=>"

let print_ty fmt = function
  | TInt -> pp_print_string fmt "int"
  | TUnit -> pp_print_string fmt "unit"
  | TProp -> 
      pp_print_string fmt "prop"

let quant fmt = function
  | `FA -> pp_print_string fmt "forall"
  | `EX -> pp_print_string fmt "exists"

let quantsep fmt kind = 
  match kind with
  | `Who | `Pangoline -> pp_print_string fmt "."
  | `Coq -> pp_print_string fmt ","

let prover fmt = function
  | `Pangoline -> pp_print_string fmt "pangoline"
  | `Coq -> pp_print_string fmt "coq"
let choice fmt = function
  | Predefined -> pp_print_string fmt "predefined"
  | Include s -> printf "\"%s\"" s
  | TakeOver -> pp_print_string fmt "takeover"
let takeover fmt (p,c) = fprintf fmt "%a %a" prover p choice c
let compare a b = 
  match a,b with
  | Int i1, Int i2 -> Big_int.compare_big_int i1 i2
  | _, _ -> Pervasives.compare a b

