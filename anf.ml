open Ty
open Ast
open Recon

let new_var = 
  let cnt = ref 0 in
  fun () -> Printf.sprintf "-tmp%d" !cnt

let id x = x
let rec normalize_term v = normalize v id
and normalize e k =
  let loc = e.loc in
  match e.v with
  | (Const _ | Var _ | Axiom _ | Logic _ | Quant _ | Param _ ) -> k e
  | For _ -> assert false
  | Lam (x,t,p,e,q) -> k (lam x t p (normalize_term e) q loc)
  | PureFun (x,t,e)-> k (plam x t (normalize_term e) loc)
  | Let (g,e1,x,e2,r) ->
      normalize e1 (fun v -> let_ g v x (normalize e2 k) r loc)
  | LetReg (l,e) -> k (letreg l e loc)
  | TypeDef (g,t,v,e) -> k (typedef g t v e loc)
  | Ite (e1,e2,e3) ->
      normalize_name e1
        (fun v -> k (ite v (normalize_term e2) (normalize_term e3) loc))
  | Annot (e,_) -> normalize e k
  | App (e1,e2,f,c) ->
      (* impure application *)
      normalize_name e1
        (fun v1 -> normalize_name e2 (fun v2 -> allapp v1 v2 f c loc))

and normalize_name e k =
  normalize e
    (fun e -> 
      if is_value_node e then k e else
        let nv = new_var () in
        let nvv = svar nv e.t e.loc in
        let_ Generalize.empty e nv (k nvv) NoRec e.loc)
