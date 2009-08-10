open Vars
open Clean_ast
module O = Ast
module SM = Misc.StringMap
module U = Unify
module VM = Var.FreeMap
module TM = TyVar.FreeMap

type env = 
  { names : Var.t SM.t;
    types : (TyVar.t list * Ty.t) VM.t;
    n : int
  }

let add_var env x tl t =
  let nv = Var.from_string x in
  { env with names = SM.add x nv env.names;
    types = VM.add nv (tl,t) env.types }, nv

let get_var env x = 
  let v = SM.find x env.names in
  v, VM.find v env.types

exception Error of string

let error s = raise (Error s)


let ty,gen_vars =
  let h = U.H.create 127 in
  let rec ty' = function
    | U.Var _ -> Ty.var (TyVar.from_string "a")
    | U.Arrow (t1,t2) -> Ty.arrow (ty t1) (ty t2)
    | U.Const c -> Ty.const c
  and ty x = 
    try U.H.find h x 
    with Not_found -> 
      let r = ty' (Unionfind.desc x) in
      U.H.add h x r; r in

  let gen_vars env oldt = 
    let n = env.n in
    let s = U.H.create 17 in
    let add k = if U.H.mem s k then () else U.H.add s k () in
    let rec aux x = 
      match Unionfind.desc x with
      | U.Var k when k > n -> add x
      | U.Var _ | U.Const _ -> ()
      | U.Arrow (t1,t2) -> aux t1; aux t2
    in
    aux oldt;
    U.H.fold (fun k () acc -> 
      (match U.H.find h k with | Ty.Var x -> x | _-> assert false) :: acc) s [] in
  ty, gen_vars

let getinst tl oldt newt = 
  let rec aux acc t1 t2 = 
    match t1,t2 with
    | Ty.Const c1, Ty.Const c2 when c1 = c2 -> acc
    | Ty.Tuple (ta1,ta2), Ty.Tuple (tb1,tb2) 
    | Ty.Arrow (ta1,ta2), Ty.Arrow (tb1,tb2) -> 
        aux (aux acc ta1 ta2) tb1 tb2
    | Ty.Var x, _ -> 
        begin try 
          let t = TM.find x acc in
          assert (Ty.equal t t2); acc
        with Not_found -> TM.add x t2 acc end
    | _ -> assert false in
  let m = aux TM.empty oldt newt in
  List.map (fun x -> TM.find x m) tl


let rec recon' env t = function
  | Var x -> 
      begin try 
        let v,(tl,xt) = get_var env x in
        let tappl = getinst tl xt t in
        O.Var (v, tappl)
      with Not_found -> error (Misc.mysprintf "unknown variable :%s" x)
      end
  | Const c -> O.Const c
  | App (e1,e2) -> O.App (recon env e1, recon env e2)
  | Lam (x,e) -> 
      let t = Ty.arg t in
      let env, nv = add_var env x [] t in
      O.Lam (t,O.close_bind nv (recon env e))
  | Let (e1,x,e2) ->
      let t1 = ty e1.t in
      let tl = gen_vars env e1.t in
      let env1 = { env with n = 1 + env.n } in
      let e1 = recon env1 e1 in
      let env2,nv = add_var env x tl t1 in
      O.Let (O.close_tygen tl e1, 
             O.close_bind nv (recon env2 e2))
and recon env t = 
  let nt = ty t.t in
  { O.v = recon' env nt t.v; t = nt }

let term t = recon { names = Initial.intern_map; types = VM.empty; n = 0 } t

