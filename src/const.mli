type ty = 
  | TInt
  | TProp


type t = 
  | Int of Big_int.big_int
  | Ptrue
  | Pfalse

val hash_t : ty -> int

val compare : t -> t -> int

val type_of_constant : t -> ty

type 'a isrec = 
  | LogicDef
  | NoRec
  | Rec of 'a

type takeover = [`Coq | `Pangoline ] * choice
and choice = 
  | Include of string
  | TakeOver 
  | Predefined

val print_ty : [`Coq | `Who | `Pangoline ] -> ty Myformat.fmt
val print : t Myformat.fmt
val funsep : [`Coq | `Who | `Pangoline ] Myformat.fmt
val quant : [`FA | `EX ] Myformat.fmt
val quantsep : [`Coq | `Who | `Pangoline ] Myformat.fmt
val takeover : takeover Myformat.fmt

