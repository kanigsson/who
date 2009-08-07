type node = int

let const c = U (Const c)
let var n = U (Var (n))

let arrow t1 t2 = U (Arrow (t1,t2))
