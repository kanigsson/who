open Clean_ast
module O = Ast
module SM = Misc.StringMap
module U = Unify

type env = { types : (tvar list * Ty.t) SM.t }

let add_var env x tl t = { types = SM.add x (tl,t) env.types }

let type_of_var env x = SM.find x env.types

exception Error of string

let error s = raise (Error s)


let ty =
  let h = U.H.create 127 in
  let rec ty' = function
    | Ty.Var s -> Ty.var s
    | Ty.Arrow (t1,t2) -> Ty.arrow (ty t1) (ty t2)
    | Ty.Tuple (t1,t2) -> Ty.tuple (ty t1) (ty t2)
    | Ty.Const c -> Ty.const c
  and ty x = 
    try U.H.find h x 
    with Not_found -> 
      match Unionfind.desc x with
      | U.U _ -> assert false
      | U.T t -> 
          let r = ty' t in
          U.H.add h x r; r in
  ty

let getinst tl oldt newt = 
  let rec aux acc t1 t2 = 
    let Ty.C t1' = t1 and Ty.C t2' = t2 in
    match t1',t2' with
    | Ty.Const c1, Ty.Const c2 when c1 = c2 -> acc
    | Ty.Tuple (ta1,ta2), Ty.Tuple (tb1,tb2) 
    | Ty.Arrow (ta1,ta2), Ty.Arrow (tb1,tb2) -> aux (aux acc ta1 tb1) ta2 tb2
    | Ty.Var x, _ -> 
        begin try 
          let t = SM.find x acc in
          assert (t = t2); acc
        with Not_found -> SM.add x t2 acc end
    | _, _ -> assert false in
  let m = aux SM.empty oldt newt in
  List.map (fun x -> SM.find x m) tl


let rec recon' env t = function
  | Var x -> 
      begin try 
        let tl,xt = type_of_var env x in
        let tappl = getinst tl xt t in
        O.Var (x, tappl)
      with Not_found -> error (Misc.mysprintf "unknown variable :%s" x)
      end
  | Const c -> O.Const c
  | App (e1,e2) -> O.App (recon env e1, recon env e2)
  | Lam (x,ot,e) -> 
      O.Lam (x,ot, recon (add_var env x [] ot) e)
  | Let (tl,e1,x,e2) ->
      let t1 = ty e1.t in
      let env' = add_var env x tl t1 in
      O.Let (tl, recon env e1, x, recon env' e2)
and recon env t = 
  let nt = ty t.t in
  { O.v = recon' env nt t.v; t = nt }

let term t = recon { types = Initial.typing_env } t

