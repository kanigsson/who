open Vars
module I = Ast.DontCare
module O = Ast.Ty
open Ast

let rec recon' = function
  | Var x -> Var x
  | Const c -> Const c
  | App (e1,e2) -> App (recon e1, recon e2)
  | Lam b -> 
      let x,e = I.open_bind b in
      Lam (close_bind x (recon e))
  | Let (e1,b) ->
      let x,e2 = I.open_bind b in
      Let (recon e1, close_bind x recon e2)
and recon t = 
  le

