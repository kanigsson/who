open Ty
open Ast
open Recon

let id x = x
let rec normalize_term v = normalize v id
and normalize e k =
  let loc = e.loc in
  match e.v with
  | (Const _ | Ast.Var _ | Axiom _ | Logic _ | Quant _ | Param _ ) -> k e
  | For _ | Gen _ -> assert false
  | Lam (x,t,cap,p,e,q) -> k (caplam x t cap p (normalize_term e) q loc)
  | PureFun (t,(_,x,e))-> k (plam x t (normalize_term e) loc)
  | Let (p,g,e1,(_,x,e2),r) -> 
(*       Myformat.printf "normalizing let: %a@." Name.print x; *)
      normalize e1 (fun v -> let_ ~prelude:p g v x (normalize e2 k) r loc)
  | Section (n,f,e) -> k (section n f (normalize_term e) loc)
  | EndSec e -> k (endsec (normalize_term e) loc)
  | LetReg (l,e) -> k (letreg l (normalize_term e) loc)
  | TypeDef (g,t,v,e) -> k (typedef g t v (normalize_term e) loc)
  | Ite (e1,e2,e3) ->
      normalize_name e1
        (fun v -> k (ite v (normalize_term e2) (normalize_term e3) loc))
  | Annot (e,_) -> normalize e k
  | App (e1,e2,f,c) ->
      normalize_name e1
        (fun v1 -> normalize_name e2 
          (fun v2 -> k (allapp v1 v2 f c loc)))

and normalize_name e k =
  normalize e
    (fun e -> 
      if is_value_node e then k e 
      else
        let nv = Name.from_string "anf" in
        let nvv = svar nv e.t e.loc in
        let_ Generalize.empty e nv (k nvv) NoRec e.loc)
