open Vars
module U = Unify

type quant = FA | EX
type ('a,'b,'c) t'' =
  | Const of Const.t
  | Var of var * ('a,'b,'c) Inst.t
  | App of ('a,'b,'c) t' * ('a,'b,'c) t' * fix
  | Lam of 
      var * Ty.t * ('a,'b,'c) t' option * ('a,'b,'c) t' * ('a,'b,'c) post 
  | Let of Ty.Generalize.t * ('a,'b,'c) t' * var * ('a,'b,'c) t' * isrec
  | PureFun of var * Ty.t * ('a,'b,'c) t'
  | Ite of ('a,'b,'c) t' * ('a,'b,'c) t' * ('a,'b,'c) t'
  | Axiom of ('a,'b,'c) t'
  | Logic of Ty.t
  | Annot of ('a,'b,'c) t' * Ty.t
  | TypeDef of Ty.Generalize.t * Ty.t option * var * ('a,'b,'c) t'
  | Quant of quant * var * Ty.t * ('a,'b,'c) t'
  | Param of Ty.t * Effect.t
  | For of var * ('a,'b,'c) t' option * var * ('a,'b,'c) t'
and ('a,'b,'c) t' = { v :('a,'b,'c)  t'' ; t : 'a ; e : 'c; loc : Loc.loc }
and ('a,'b,'c) post = 
  | PNone
  | PPlain of ('a,'b,'c) t'
  | PResult of var * ('a,'b,'c) t'
and fix = Infix | Prefix
and isrec = Rec of Ty.t | NoRec


open Myformat

let is_compound = function
  | Const _ | Var _ | Lam _ | PureFun _ | Annot _-> false
  | App _ | Let _ | Ite _ | Axiom _ | Logic _ | TypeDef _
  | Quant _ | Param _ | For _ -> true
let is_compound_node t = is_compound t.v

let print pra prb prc fmt t = 
  let rec print' fmt = function
    | Const c -> Const.print fmt c
    | Var (v,i) -> 
        if Inst.is_empty i then var fmt v
        else fprintf fmt "%a %a" var v (Inst.print pra prb prc) i
    | App ({v = App (op,t1,_)},t2,Infix) -> 
        fprintf fmt "@[%a@ %a@ %a@]" with_paren t1 print op with_paren t2
    | App (t1,t2,_) ->
          fprintf fmt "@[%a@ %a@]" print t1 with_paren t2
    | Lam (x,t,p,e,q) -> 
        fprintf fmt "@[(λ(%s:%a)@ -->@ %a@ %a@ %a)@]" x 
          Ty.print t pre p print e post q
    | PureFun (x,t,e) ->
        fprintf fmt "@[(λ(%s:%a)@ ->@ %a)@]" x Ty.print t print e
    | Let (g,e1,x,e2,r) -> 
        fprintf fmt "@[let@ %a%s %a=@[@ %a@]@ in@ %a@]" 
          prrec r x Ty.Generalize.print g print e1 print e2
    | Ite (e1,e2,e3) ->
        fprintf fmt "@[if %a then %a else %a@]" print e1 print e2 print e3
    | Axiom e -> fprintf fmt "axiom %a" print e
    | Logic t -> fprintf fmt "logic %a" Ty.print t
    | TypeDef (g,t,x,e) -> 
        fprintf fmt "type %a%a =@ %a in@ %a" 
          var x Ty.Generalize.print g (opt_print Ty.print) t print e
    | Quant (k,x,t,e) ->
        fprintf fmt "@[%a (%a:%a).@ %a@]" quant k var x Ty.print t print e
    | Param (t,e) -> fprintf fmt "param(%a,%a)" Ty.print t Effect.print e
    | For (dir,inv,i,t) ->
        fprintf fmt "%a (%a) %%start %%end (%a)" 
          var dir (opt_print print) inv print t
    | Annot (e,t) -> 
        fprintf fmt "(%a : %a)" print e Ty.print t
  and print fmt t = print' fmt t.v
  and pre fmt = function
    | None -> ()
    | Some x -> fprintf fmt "{%a}" print x
  and post fmt = function
    | PNone -> ()
    | PPlain f -> fprintf fmt "{%a}" print f
    | PResult (r,f) -> fprintf fmt "{ %a : %a}" var r print f
  and quant fmt = function
    | FA -> pp_print_string fmt "forall"
    | EX -> pp_print_string fmt "exists"
  and prrec fmt = function
    | NoRec -> ()
    | Rec t -> fprintf fmt "rec(%a) " Ty.print t
  and with_paren fmt x = 
    if is_compound_node x then paren print fmt x else print fmt x in
  print fmt t

module Infer = struct
  type t = (U.node, U.rnode, U.enode) t'

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t = mk v t (U.new_e ())
  let const c = mk_val (Const c) (U.const (Const.type_of_constant c))

  let lam x t p e q = mk_val (Lam (x,U.to_ty t,p,e,q)) (U.arrow t e.t e.e)
(*   let plam x t e = mk_val (PureFun (x,t,e)) (U.parr t e.t) *)
  let lam_anon t e p = lam "__anon" t e p

  let print fmt t = print U.print_node U.prvar U.preff fmt t

end

module Recon = struct
  type t = (Ty.t, rvar, Effect.t) t'
  let print fmt t = print Ty.print Vars.rvar Effect.print fmt t

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t loc = { v = v; t = t; e = Effect.empty; loc = loc }

  let app ?(kind=Prefix) t1 t2 loc = 
    let t = Ty.result t1.t and e = Ty.latent_effect t1.t in
    mk (App (t1,t2,kind)) t (Effect.union t1.e (Effect.union t2.e e)) loc


  let app2 t t1 t2 loc = app (app t t1 loc) t2 loc
  let appi t t1 t2 loc = app ~kind:Infix (app t t1 loc) t2 loc
  let var s inst (g,t) = mk_val (Var (s,inst)) (Ty.allsubst g inst t) 

  module T = Ty
  let iip = T.parr T.int (T.parr T.int T.prop)
  let iii = T.parr T.int (T.parr T.int T.int)
  let ppp = T.parr T.prop (T.parr T.prop T.prop)
  let svar s t = var s Inst.empty (T.Generalize.empty,t) 
  let le t1 t2 loc = appi (svar "<=" iip loc) t1 t2 loc
  let and_ t1 t2 loc = appi (svar "/\\" ppp loc) t1 t2 loc
  let encl lower i upper loc = and_ (le lower i loc) (le i upper loc) loc
  let plam x t e loc = mk_val (PureFun (x,t,e)) (T.parr t e.t) loc
  let efflam x eff e = plam x (T.map eff) e
  let lam x t p e q = mk_val (Lam (x,t,p,e,q)) (T.arrow t e.t e.e)
  let ptrue_ loc = mk_val (Const (Const.Ptrue)) T.prop loc
  let plus t1 t2 loc = appi (svar "+" iii loc) t1 t2 loc
  let one = mk_val (Const (Const.Int 1)) T.int 
  let succ t loc = plus t (one loc) loc

end

module ParseT = struct
  type t = (unit,unit,unit) t'
  let nothing fmt () = ()
  let print fmt t = print nothing nothing nothing fmt t

  let mk v loc = { v = v; t = (); e = (); loc = loc }
  let app ?(kind=Prefix) t1 t2 = mk (App (t1,t2, kind))
  let var s = mk (Var (s,Inst.empty))
  let const c = mk (Const c)
  let app2 s t1 t2 loc = app (app (var s loc) t1 loc) t2 loc
  let appi s t1 t2 loc = app ~kind:Infix (app (var s loc) t1 loc) t2 loc
  let let_ l e1 x e2 r = mk (Let (l,e1,x,e2,r)) 
  let lam x t p e q = mk (Lam (x,t,p,e,q))
  let pure_lam x t e = mk (PureFun (x,t,e))
  let typedef l t x e = mk (TypeDef (l,t,x,e))
  let quant k x t e = mk (Quant (k,x,t,e))

end

let concat t1 t2 =
  let rec aux' = function
    | Const Const.Void -> t2.v
    | Let (g,t1,x,t2,r) -> Let (g,t1,x,aux t2,r)
    | TypeDef (g,t,x,t2) -> TypeDef (g,t,x,aux t2)
    | _ -> assert false 
  and aux t = { t with v = aux' t.v } in
  aux t1
