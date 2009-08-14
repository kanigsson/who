open Vars
module U = Unify

type ('a,'b,'c) t'' =
  | Const of Const.t
  | Var of var * ('a,'b,'c) Inst.t
  | App of ('a,'b,'c) t' * ('a,'b,'c) t'
  | Lam of var * Ty.t * ('a,'b,'c) t' * ('a,'b,'c) t' option
  | Let of Generalize.t * ('a,'b,'c) t' * var * ('a,'b,'c) t'
and ('a,'b,'c) t' = { v :('a,'b,'c)  t'' ; t : 'a ; e : 'c; loc : Loc.loc }


open Myformat

let print pra prb prc fmt t = 
  let rec print' fmt = function
    | Const c -> Const.print fmt c
    | Var (v,i) -> fprintf fmt "%s %a" v (Inst.print pra prb prc) i
    | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
    | Lam (x,t,e,p) -> fprintf fmt "@[(λ(%s:%a)@ ->@ %a%a)@]" 
      x Ty.print t print e post p
    | Let (g,e1,x,e2) -> 
        fprintf fmt "@[let@ %s %a=@ %a@ in@ %a@]" 
        x Generalize.print g print e1 print e2
  and print fmt t = print' fmt t.v
  and post fmt = function
    | None -> ()
    | Some x -> fprintf fmt "{%a}" print x in 
  print fmt t

module Infer = struct
  type t = (U.node, U.rnode, U.enode) t'

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t = mk v t (U.new_e ())
  let const c = mk_val (Const c) (U.const (Const.type_of_constant c))

  let lam x t e p = mk_val (Lam (x,U.to_ty t,e,p)) (U.arrow t e.t e.e)
  let lam_anon t e p = lam "__anon" t e p

  let print fmt t = print U.print_node U.prvar U.preff fmt t
end

module Recon = struct
  type t = (Ty.t, rvar, Effect.t) t'
  let print fmt t = print Ty.print Vars.rvar Effect.print fmt t
end

module ParseT = struct
  type t = (unit,unit,unit) t'
  let nothing fmt () = ()
  let print fmt t = print nothing nothing nothing fmt t

  let mk v loc = { v = v; t = (); e = (); loc = loc }
  let app t1 t2 = mk (App (t1,t2))
  let var s = mk (Var (s,Inst.empty))
  let const c = mk (Const c)
  let app2 s t1 t2 loc = app (app (var s loc) t1 loc) t2 loc
  let let_ l e1 x e2 = mk (Let (l,e1,x,e2)) 
  let lam x t e p = mk (Lam (x,t,e,p))
end
