open Ast
open Ast.Recon

let term env t =
  rebuild_map 
    ~varfun:(fun z i def ->
      try 
        let g,t = Name.M.find z env in
        allsubst g i t
      with Not_found -> def)
    ~termfun:(fun t ->
      match t.v with
      | Let (g,e1,b,_) ->
          let x,e2 = vopen b in
          polsubst g x e1 e2
      | Const _ | Var _ | App _ | Gen _ | PureFun _ | Quant _ | Ite _ 
      | Lam _ | Annot _ | For _ | LetReg _ | Param _ -> t)
    t

let rec decl env d = 
  match d with
  | Logic _ | TypeDef _ | DLetReg _ -> env, [d]
  | Formula (n,f,k) -> env, [Formula (n, term env f, k) ]
  | Section (s,cl,th) -> 
      let env, th = theory env th in
      env, [Section (s,cl,th)]
  | Program (n,g,t,Const.LogicDef) -> Name.M.add n (g,term env t) env, []
  | Program _ -> assert false
and theory env th = 
  let env, l = Misc.list_fold_map decl env th in
  env, List.flatten l

let theory th = 
  let _, th = theory Name.M.empty th in
  th
  
