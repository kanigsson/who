open Vars
open Ast
module C = Constr

let (++) a b = C.And (a,b)
let (=~=) a b = C.Eq (a,b)

let type_of_constant = function
  | Int _ -> Ty.Int
  | Void -> Ty.Unit
  | Btrue | Bfalse -> Ty.Bool

let generate term =
  let rec aux t = function
  | Const c -> t =~= Ty.const (type_of_constant c)
  | Var x -> C.Sub (x,t)
  | App (t1,t2) ->
      C.exists (fun v -> aux (Ty.arrow v t) t1 ++ aux v t2)
  | Lam b ->
      let x,e = open_bind b in
      C.exists2 (fun x1 x2 ->
        C.let_ (C.triv_scheme x1) x (aux x2 e) ++ (Ty.arrow x1 x2 =~= t))
  | Let (e1,b) ->
      let x, e2 = open_bind b in
      C.let_ (C.mk_scheme (fun a -> a, aux a e1)) x (aux t e2) in
  C.exists (fun v -> aux v term)
