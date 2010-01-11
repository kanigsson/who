module SM = Misc.StringMap
module G = Ty.Generalize
module NM = Name.M
module IT = ParseTypes

(* the environment maps each variable name to a 
   unique name *)
type env = 
  { 
    v : Name.t SM.t ;
    t : Name.t SM.t ;
    r : Name.t SM.t ;
    e : Name.t SM.t ;
    tyrepl : (Ty.Generalize.t * Ty.t) NM.t ;
    typing : (Ty.Generalize.t * Ty.t) NM.t
  }

let empty = 
  { v = SM.empty; t = SM.empty; 
    r = SM.empty; e = SM.empty;
    tyrepl = NM.empty;
    typing = NM.empty ;
  }

exception UnknownVar of string
let error s = raise (UnknownVar s)
let gen_var s m x = try SM.find x m with Not_found -> error (s ^ " var: " ^ x)

let var env = gen_var "program" env.v
let tyvar env = gen_var "type" env.t
let rvar env = gen_var "region" env.r
let effvar env = gen_var "effect" env.e

let add_var env x = 
  let y =
    try SM.find x Predefined.Logic.map
    with Not_found -> Name.from_string x in
  { env with v = SM.add x y env.v }, y

let add_ex_var env x y = 
  { env with v = SM.add x y env.v }

let add_tvar env x g t = 
  let y = 
    try SM.find x Predefined.Ty.map
    with Not_found -> Name.from_string x in
  { env with t = SM.add x y env.t;
    tyrepl = 
       match t with
       | None -> env.tyrepl
       | Some t -> NM.add y (g,t) env.tyrepl
  }, y

let add_rvars env l = 
  let r, nl = 
    List.fold_left
      (fun (r,l) x ->
        let nv = Name.from_string x in
        SM.add x nv r, nv::l) (env.r,[]) l in
  { env with r = r }, nl

let add_tvars env l = 
  List.fold_left (fun (acc,l) x -> 
    let env, nv = add_tvar acc x Ty.Generalize.empty None in
    env, nv::l) (env,[]) l

let add_evars env l = 
  let e, nl = 
    List.fold_left
      (fun (e,l) x ->
        let nv = Name.from_string x in
        SM.add x nv e, nv::l) (env.e,[]) l in
  { env with e = e }, nl

let add_gen env (tl,rl,el) =
  let env, tl = add_tvars env tl in
  let env, rl = add_rvars env rl in
  let env, el = add_evars env el in
  env, (List.rev tl,List.rev rl,List.rev el)

let effect env (rl,el) = 
  NEffect.from_lists
    (List.map (rvar env) rl)
    (List.map (effvar env) el)

let ty env t = 
  let rec aux = function
    | IT.TVar v -> Ty.var (tyvar env v)
    | IT.TConst c -> Ty.const c
    | IT.Tuple (t1,t2) -> Ty.tuple (aux t1) (aux t2)
    | IT.Arrow (t1,t2,e,cap) -> 
        Ty.caparrow (aux t1) (aux t2) (effect env e) (List.map (rvar env) cap)
    | IT.PureArr (t1,t2) -> Ty.parr (aux t1) (aux t2)
    | IT.TApp (v,i) -> 
        let v = tyvar env v in
        let i = inst i in
        begin try 
          let g,t = NM.find v env.tyrepl in
          Ty.allsubst g i t
        with Not_found -> Ty.app v i end
    | IT.Ref (r,t) -> Ty.ref_ (rvar env r) (aux t)
    | IT.Map e -> Ty.map (effect env e)
    | IT.ToLogic t -> Ty.to_logic_type (aux t)
  and inst i = Inst.map aux (rvar env) (effect env) i in
  aux t

let rec_ env = function
  | Const.Rec t -> Const.Rec (ty env t)
  | Const.NoRec -> Const.NoRec
  | Const.LogicDef -> Const.LogicDef
