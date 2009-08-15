open Vars
module U = Unify

type ('a,'b,'c) t'' =
  | Const of Const.t
  | Var of var * ('a,'b,'c) Inst.t
  | App of ('a,'b,'c) t' * ('a,'b,'c) t'
  | Lam of var * Ty.t * ('a,'b,'c) t' option * ('a,'b,'c) t' * ('a,'b,'c) post
  | Let of Ty.Generalize.t * ('a,'b,'c) t' * var * ('a,'b,'c) t'
  | PureFun of var * Ty.t * ('a,'b,'c) t'
  | Ite of ('a,'b,'c) t' * ('a,'b,'c) t' * ('a,'b,'c) t'
  | Axiom of ('a,'b,'c) t'
  | Logic of Ty.t
  | TypeDef of Ty.Generalize.t * Ty.t option * var * ('a,'b,'c) t'
and ('a,'b,'c) t' = { v :('a,'b,'c)  t'' ; t : 'a ; e : 'c; loc : Loc.loc }
and ('a,'b,'c) post = 
  | PNone
  | PPlain of ('a,'b,'c) t'
  | PResult of var * ('a,'b,'c) t'


open Myformat

let print pra prb prc fmt t = 
  let rec print' fmt = function
    | Const c -> Const.print fmt c
    | Var (v,i) -> fprintf fmt "%s %a" v (Inst.print pra prb prc) i
    | App (t1,t2) -> fprintf fmt "@[(%a@ %a)@]" print t1 print t2
    | Lam (x,t,p,e,q) -> 
        fprintf fmt "@[(λ(%s:%a)@ ->@ %a%a%a)@]" x Ty.print t 
          pre p print e post q
    | PureFun (x,t,e) ->
        fprintf fmt "@[(λ(%s:%a)@ ->@ %a)@]" x Ty.print t print e
    | Let (g,e1,x,e2) -> 
        fprintf fmt "@[let@ %s %a=@ %a@ in@ %a@]" 
          x Ty.Generalize.print g print e1 print e2
    | Ite (e1,e2,e3) ->
        fprintf fmt "@[if %a then %a else %a@]" print e1 print e2 print e3
    | Axiom e -> fprintf fmt "axiom %a" print e
    | Logic t -> fprintf fmt "logic %a" Ty.print t
    | TypeDef (g,t,x,e) -> 
        fprintf fmt "type %a =@ %a in@ %a" var x (opt_print Ty.print) t print e
  and print fmt t = print' fmt t.v
  and pre fmt = function
    | None -> ()
    | Some x -> fprintf fmt "{%a}" print x
  and post fmt = function
    | PNone -> ()
    | PPlain f -> fprintf fmt "{%a}" print f
    | PResult (r,f) -> fprintf fmt "{ %a : %a}" var r print f in
   
  print fmt t

module Infer = struct
  type t = (U.node, U.rnode, U.enode) t'

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t = mk v t (U.new_e ())
  let const c = mk_val (Const c) (U.const (Const.type_of_constant c))

  let lam x t p e q = mk_val (Lam (x,U.to_ty t,p,e,q)) (U.arrow t e.t e.e)
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
  let lam x t p e q = mk (Lam (x,t,p,e,q))
  let pure_lam x t e = mk (PureFun (x,t,e))
  let typedef l t x e = mk (TypeDef (l,t,x,e))
end
