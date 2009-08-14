open I_ast
module O = Ast
module SM = Misc.StringMap
module U = Unify

type env = { types : ((tvar list * rvar list * effvar list) * Ty.t) SM.t }

let add_var env x g t = { types = SM.add x (g,t) env.types }

let type_of_var env x = SM.find x env.types

exception Error of string

let error s = raise (Error s)

let getinst (tl,rl,el) oldt newt = 
  let rec aux ((vm,rm,em) as acc) t1 t2 = 
    let Ty.C t1' = t1 and Ty.C t2' = t2 in
    match t1',t2' with
    | Ty.Const c1, Ty.Const c2 when c1 = c2 -> acc
    | Ty.Arrow (ta1,ta2,eff1), Ty.Arrow (tb1,tb2,eff2) -> 
        auxe (aux (aux acc ta1 tb1) ta2 tb2) eff1 eff2
    | Ty.Tuple (ta1,ta2), Ty.Tuple (tb1,tb2) ->
        aux (aux acc ta1 tb1) ta2 tb2
    | Ty.Var x, _ -> 
        begin try 
          let t = SM.find x vm in
          assert (t = t2); acc
        with Not_found -> SM.add x t2 vm, rm, em end
    | Ty.Ref (r1,t1), Ty.Ref (r2,t2) ->
        begin try
          let r' = SM.find r1 rm in
          assert (r' = r2); acc
        with Not_found -> vm, SM.add r1 r2 rm, em end
    | _, _ -> assert false 
  and auxe acc eff1 eff2 = acc in
  let vm,rm,em = aux (SM.empty, SM.empty, SM.empty) oldt newt in
  List.map (fun x -> SM.find x vm) tl,
  List.map (fun r -> SM.find r rm) rl,
  []


let rec recon' t = function
  | Var (x,i) -> O.Var (x,inst i)
  | Const c -> O.Const c
  | App (e1,e2) -> O.App (recon e1, recon e2)
  | Lam (x,ot,e,_) -> O.Lam (x,ot, recon e)
  | Let (g,e1,x,e2) ->
      O.Let (g, recon e1, x, recon e2)
and recon t = 
  let nt = U.to_ty t.t in
  { O.v = recon' nt t.v; t = nt }
and inst (th,rh,eh) =
    List.map U.to_ty th, List.map U.to_r rh, List.map U.to_eff eh

let term t = recon t

