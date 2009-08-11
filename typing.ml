open Ast
open Ty
module SM = Misc.StringMap

exception Error of string

let error s = raise (Error s)

type env = { types : (tvar list * Ty.t) SM.t }

let add_var env x tl t = { types = SM.add x (tl,t) env.types }

let type_of_var env x = SM.find x env.types


let rec typing' env = function
  | Ast.Const c -> Ty.const (Const.type_of_constant c)
  | Ast.Var (s,tl) -> 
      begin try 
        let tvl, t = type_of_var env s in
        Ty.lsubst tvl tl t
      with Not_found -> error (Misc.mysprintf "unknown variable: %s" s) end
  | App (e1,e2) ->
      let t2 = typing env e2 in
      begin match typing env e1 with
      | C (Arrow (ta,tb)) -> 
          if ta = t2 then tb else error "type mismatch"
      | _ -> error "no function type"
      end
  | Lam (x,t,e) ->
      let env = add_var env x [] t in
      let t' = typing env e in
      arrow t t'
  | Let (tl,e1,x,e2) ->
      let t = typing env e1 in
      let env = add_var env x tl t in
      typing env e2
and typing env { v = v; t = t } =
  let t' = typing' env v in
  if t = t' then t else error "annotation mismatch"

let typing t = ignore (typing { types = Initial.typing_env; } t)
