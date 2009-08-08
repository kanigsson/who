open Vars
open Clean_ast
module O = Ast
module SM = Misc.StringMap
module U = Unify

type env = 
  { names : Var.t SM.t;
    n : int
  }

let add_var env x =
  let nv = Var.from_string x in
  { env with names = SM.add x nv env.names }, nv

let get_var env x = SM.find x env.names

exception Error of string

let error s = raise (Error s)


let ty,gen_vars =
  let h = U.H.create 127 in
  let rec ty' x = match Unionfind.desc x with
                  | U.Var _ -> Ty.var (TyVar.from_string "a")
                  | U.Arrow (t1,t2) -> Ty.arrow (ty t1) (ty t2)
                  | U.Const c -> Ty.const c
  and ty (U.U x) = try U.H.find h x 
                   with Not_found -> 
                     let r = ty' x in
                     U.H.add h x r; r in

  let gen_vars env oldt = 
    let n = env.n in
    let s = U.H.create 17 in
    let add k = if U.H.mem s k then () else U.H.add s k () in
    let rec aux (U.U x) = 
      match Unionfind.desc x with
      | U.Var k when k > n -> add x
      | U.Var _ | U.Const _ -> ()
      | U.Arrow (t1,t2) -> aux t1; aux t2
    in
    aux oldt;
    U.H.fold (fun k () acc -> 
      (match U.H.find h k with | `U `Var x -> x | _-> assert false) :: acc) s [] in
  ty, gen_vars

let rec recon' env t = function
  | Var x -> 
      begin try O.Var (get_var env x)
      with Not_found -> error (Misc.mysprintf "unknown variable :%s" x)
      end
  | Const c -> O.Const c
  | App (e1,e2) -> O.App (recon env e1, recon env e2)
  | Lam (x,e) -> 
      let env, nv = add_var env x in
      O.Lam (Ty.arg t, O.close_bind nv (recon env e))
  | Let (e1,x,e2) ->
      ignore (ty e1.t);
      let vars = gen_vars env e1.t in
      let env1 = { env with n = 1 + env.n } in
      let e1 = recon env1 e1 in
      let env2,nv = add_var env x in
      O.Let (O.close_tygen vars e1, 
             O.close_bind nv (recon env2 e2))
and recon env t = 
  let nt = ty t.t in
  { O.v = recon' env nt t.v; t = nt }

let term t = recon { names = Initial.intern_map; n = 0 } t

