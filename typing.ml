open I_ast
open Ty
module SM = Misc.StringMap

exception Error of string

let error s = raise (Error s)

type env = { types : (Generalize.t * Ty.t) SM.t }

let add_var env x g t = { types = SM.add x (g,t) env.types }

let type_of_var env x = SM.find x env.types

open Format
let rec typing' env = function
  | I_ast.Const c -> 
      Ty.const (Const.type_of_constant c), Effect.empty
  |I_ast.Var (s,i) -> 
      begin try 
        let g, t = type_of_var env s in
        Ty.allsubst g i t, Effect.empty
      with Not_found -> error (Myformat.sprintf "unknown variable: %s" s) end
  | App (e1,e2) ->
      let t2,eff2 = typing env e2 in
      begin match typing env e1 with
      | C (Arrow (ta,tb,eff)), eff1 -> 
          if ta = t2 then tb, Effect.union eff1 (Effect.union eff2 eff) 
          else error "type mismatch"
      | C (PureArr (ta,tb)), eff ->
          if ta = t2 then tb, eff else error "type mismatch"
      | _ -> error "no function type"
      end
  | Lam (x,t,e,p) ->
      let env = add_var env x ([],[],[]) t in
      let t',eff = typing env e in
      arrow t t' eff, Effect.empty
  | Let (tl,e1,x,e2) ->
      let t,eff1 = typing env e1 in
      let env = add_var env x tl t in
      let t, eff2 = typing env e2 in
      t, Effect.union eff1 eff2
and typing env { v = v; t = t } =
  let t',eff = typing' env v in
  if Ty.equal t t' then t,eff else 
    error (Myformat.sprintf "annotation mismatch: %a and %a@." Ty.print t Ty.print t')

let typing t = ignore (typing { types = Initial.typing_env; } t)
