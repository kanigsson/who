open Ast
open Ty
module SM = Misc.StringMap

exception Error of string

let error s = raise (Error s)

type env = { types : (Generalize.t * Ty.t) SM.t }

let add_var env x g t = { types = SM.add x (g,t) env.types }

let type_of_var env x = SM.find x env.types

open Format
(* TODO logic typing *)
let rec typing' env  = function
  | Ast.Const c -> 
      Ty.const (Const.type_of_constant c), Effect.empty
  |Ast.Var (s,i) -> 
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
  | Lam (x,t,p,e,q) ->
      let env = add_var env x Generalize.empty t in
      let t',eff = typing env e in
      arrow t t' eff, Effect.empty
  | Let (tl,e1,x,e2) ->
      let t,eff1 = typing env e1 in
      let env = add_var env x tl t in
      let t, eff2 = typing env e2 in
      t, Effect.union eff1 eff2
  | TypeDef (tl,t,x,e) ->
      typing env e
  | PureFun (x,t,e) ->
      let env = add_var env x Generalize.empty t in
      let t', eff = typing env e in
      if Effect.is_empty eff then parr t t', eff 
      else error "effectful pure function"
  | Axiom e ->
      let t, eff = typing env e in
      t,eff
  | Logic t -> t, Effect.empty
  | Ite (e1,e2,e3) ->
      let t1, eff1 = typing env e1 in
      if Ty.equal t1 Ty.bool then
        let t2, eff2 = typing env e2 in
        let t3, eff3 = typing env e3 in
        if Ty.equal t2 t3 then t2, Effect.union eff1 (Effect.union eff2 eff3)
        else error "mismatch on if branches"
      else error "condition is not of boolean type"

and typing env (e : Ast.Recon.t) : Ty.t * Effect.t =
  let ((t',eff) as x) = typing' env e.v in
  if Ty.equal e.t t' then x else 
    error (Myformat.sprintf "annotation mismatch: %a and %a@." 
             Ty.print e.t Ty.print t')

let typing t = ignore (typing { types = Initial.typing_env; } t)
