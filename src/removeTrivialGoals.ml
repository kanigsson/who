open Ast

module Env : sig
  type t
  val empty : t
  val add_hypo : t -> Ast.t -> t
  val mem : t -> Ast.t -> bool
end = struct
  type t = Ast.t list
  let empty = []
  let add_hypo env x = x ::env
  let mem env x = ExtList.mem Ast.equal x env
end

let rec term env f = 
  match f.v with
  | Quant (k, t,b) ->
      let x , f' = vopen b in
      squant k x t (term env f') f.loc
  | Ast.Gen (g,f') -> 
      gen g (term env f') f.loc
  | f' -> 
      begin match destruct_app2_var' f' with
      | Some (v,_,f1,f2) when PL.equal v PI.impl_id  -> 
          impl f1 (term (Env.add_hypo env f1) f2) f.loc
      | Some (v,_,f1,f2) when PL.equal v PI.and_id  -> 
          and_ (term env f1) (term env f2) f.loc
      | _ -> if Env.mem env f then ptrue_ f.loc else f
      end

let declfun d = match d with
| Formula (s,t,`Proved) ->
    [ Formula (s,term Env.empty t, `Proved) ]
| _ -> [d]

let theory th = 
  theory_map ~varfun:Misc.k3 ~termfun:Misc.id ~declfun th
