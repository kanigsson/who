type node = int

type 'a t' = 
  | Var of int
  | Const of Ty.const
  | Arrow of 'a * 'a

type t = U of t t'

let const c = U (Const c)
let var n = U (Var (n))

let arrow t1 t2 = U (Arrow (t1,t2))
