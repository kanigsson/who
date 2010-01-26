open Ty
open Ast
open Recon

let id x = x
let rec normalize_term v = normalize v id
and normalize e k =
  let loc = e.loc in
  match e.v with
  | (Const _ | Ast.Var _ | Param _ ) -> k e
  | For _ -> assert false
  | Lam (x,t,cap,(p,e,q)) -> 
(*       Format.printf "found effectful function %a@." Name.print x; *)
      k (caplam x t cap (pre p) 
        (normalize_term e) (post q) loc)
  | PureFun (t,(_,x,e))-> k (plam x t (normalize_term e) loc)
  | Let (g,e1,(_,x,e2),r) -> 
      normalize e1 (fun v -> let_ g v x (normalize e2 k) r loc)
  | LetReg (l,e) -> k (letreg l (normalize_term e) loc)
  | Gen (g,e) -> k (gen g (normalize_term e) loc)
  | Quant (kind,t,(_,x,e)) -> k (squant kind x t (normalize_term e) loc)
  | Ite (e1,e2,e3) ->
      normalize_name e1
        (fun v -> k (ite ~logic:false v (normalize_term e2) (normalize_term e3) loc))
  | Annot (e,_) -> normalize e k
  | App (e1,e2,f,c) ->
(*       Format.printf "applying: %a@." print e1; *)
      normalize_name e1
        (fun v1 -> normalize_name e2 
          (fun v2 -> k (allapp v1 v2 f c loc)))
  | HoareTriple (p,e,q) -> 
(*       Format.printf "found hoare_triple@."; *)
      k (hoare_triple (pre p) (normalize_term e) (post q) loc)
and pre (cur,p) =
(*   Format.printf "in precondition@."; *)
  cur, Opt.map normalize_term p
and post (old,cur,p) =
  let p = 
    match p with
    | PNone | PResult _ -> assert false
    | PPlain f -> PPlain (normalize_term f) in
  old, cur, p

and normalize_name e k =
  normalize e
    (fun e -> 
      if is_value e then k e 
      else
        let nv = Name.from_string "anf" in
        let nvv = svar nv e.t e.loc in
        let_ Generalize.empty e nv (k nvv) Const.NoRec e.loc)

let term = normalize_term

let rec decl d = 
  match d with
  | Logic _ | TypeDef _ | DLetReg _ | DGen _ -> d 
  | Formula (s,t,r) -> Formula (s, term t, r)
  | Section (s,cl, th) -> Section (s,cl, theory th)
  | Program (n,g,t,r) -> Program (n,g,term t, r)

and theory th = List.map decl th