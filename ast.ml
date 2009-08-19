open Vars
module U = Unify
module C = Const

type ('a,'b,'c) t'' =
  | Const of Const.t
  | Var of Var.t * ('a,'b,'c) Inst.t
  | App of ('a,'b,'c) t' * ('a,'b,'c) t' * Const.fix * RVar.t list
  | Lam of 
      Var.t * Ty.t * ('a,'b,'c) pre * ('a,'b,'c) t' * ('a,'b,'c) post 
  | Let of Ty.Generalize.t * ('a,'b,'c) t' * Var.t * ('a,'b,'c) t' * isrec
  | PureFun of Var.t * Ty.t * ('a,'b,'c) t'
  | Ite of ('a,'b,'c) t' * ('a,'b,'c) t' * ('a,'b,'c) t'
  | Axiom of ('a,'b,'c) t'
  | Logic of Ty.t
  | Annot of ('a,'b,'c) t' * Ty.t
  | TypeDef of Ty.Generalize.t * Ty.t option * TyVar.t * ('a,'b,'c) t'
  | Quant of Const.quant * Var.t * Ty.t * ('a,'b,'c) t'
  | Param of Ty.t * Effect.t
  | For of Var.t * ('a,'b,'c) pre * Var.t * Var.t * Var.t * ('a,'b,'c) t'
  | LetReg of RVar.t list * ('a,'b,'c) t'
and ('a,'b,'c) t' = { v :('a,'b,'c)  t'' ; t : 'a ; e : 'c; loc : Loc.loc }
and ('a,'b,'c) post' = 
  | PNone
  | PPlain of ('a,'b,'c) t'
  | PResult of Var.t * ('a,'b,'c) t'
and ('a,'b,'c) pre = Var.t * ('a,'b,'c) t' option
and ('a,'b,'c) post = Var.t * Var.t * ('a,'b,'c) post'
and isrec = Rec of Ty.t | NoRec


open Myformat

let is_compound = function
  | Const _ | Var _ | Lam _ | PureFun _ | Annot _-> false
  | App _ | Let _ | Ite _ | Axiom _ | Logic _ | TypeDef _
  | Quant _ | Param _ | For _ | LetReg _ -> true
let is_compound_node t = is_compound t.v

let print pra prb prc fmt t = 
  let rec print' fmt = function
    | Const c -> Const.print fmt c
    | Var (v,i) -> 
        if Inst.is_empty i then Var.print fmt v
        else fprintf fmt "%a %a" Var.print v (Inst.print pra prb prc) i
    | App ({v = App (op,t1,_,_)},t2,C.Infix,_) -> 
        fprintf fmt "@[%a@ %a@ %a@]" with_paren t1 print op with_paren t2
    | App (t1,t2,_,cap) ->
          fprintf fmt "@[%a%a@ %a@]" print t1 maycap cap with_paren t2
    | Lam (x,t,p,e,q) -> 
        fprintf fmt "@[(λ(%a:%a)@ -->@ %a@ %a@ %a)@]" Var.print x 
          Ty.print t pre p print e post q
    | PureFun (x,t,e) ->
        fprintf fmt "@[(λ(%a:%a)@ ->@ %a)@]" Var.print x Ty.print t print e
    | Let (g,e1,x,e2,r) -> 
        fprintf fmt "@[let@ %a%a %a=@[@ %a@]@ in@ %a@]" 
          prrec r Var.print x Ty.Generalize.print g print e1 print e2
    | Ite (e1,e2,e3) ->
        fprintf fmt "@[if %a then %a else %a@]" print e1 print e2 print e3
    | Axiom e -> fprintf fmt "axiom %a" print e
    | Logic t -> fprintf fmt "logic %a" Ty.print t
    | TypeDef (g,t,x,e) -> 
        fprintf fmt "type %a%a =@ %a in@ %a" 
          TyVar.print x Ty.Generalize.print g (opt_print Ty.print) t print e
    | Quant (k,x,t,e) ->
        fprintf fmt "@[%a (%a:%a).@ %a@]" C.quant k Var.print x Ty.print t print e
    | Param (t,e) -> fprintf fmt "param(%a,%a)" Ty.print t Effect.print e
    | For (dir,inv,i,st,en,t) ->
        fprintf fmt "%a (%a) %a %a (%a)" 
          Var.print dir pre inv Var.print st Var.print en print t
    | Annot (e,t) -> fprintf fmt "(%a : %a)" print e Ty.print t
    | LetReg (v,t) -> 
        fprintf fmt "@[letregion %a in@ %a@]" 
          (print_list space RVar.print) v print t
      
  and print fmt t = print' fmt t.v
  and pre fmt (_,x) = 
    match x with
    | None -> ()
    | Some x -> fprintf fmt "{%a}" print x
  and post fmt (_,_,x) = 
    match x with
    | PNone -> ()
    | PPlain f -> fprintf fmt "{%a}" print f
    | PResult (r,f) -> fprintf fmt "{ %a : %a}" Var.print r print f
  and prrec fmt = function
    | NoRec -> ()
    | Rec t -> fprintf fmt "rec(%a) " Ty.print t
  and maycap fmt = function
    | [] -> ()
    | l -> fprintf fmt "{%a}" (print_list space RVar.print) l
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
  let lam_anon t e p = lam (Var.new_anon ()) t e p

  let print fmt t = print U.print_node U.prvar U.preff fmt t

end

module Recon = struct
  type t = (Ty.t, RVar.t, Effect.t) t'
  let print fmt t = print Ty.print RVar.print Effect.print fmt t

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t loc = { v = v; t = t; e = Effect.empty; loc = loc }

  let app ?(kind=C.Prefix) ?(cap=[]) t1 t2 loc = 
    let t = Ty.result t1.t and e = Ty.latent_effect t1.t in
    mk (App (t1,t2,kind,cap)) t (Effect.union t1.e (Effect.union t2.e e)) loc


  let app2 t t1 t2 loc = app (app t t1 loc) t2 loc
  let appi t t1 t2 loc = app ~kind:C.Infix (app t t1 loc) t2 loc
  let allapp t1 t2 kind cap loc = app ~kind ~cap t1 t2 loc
  let var s inst (g,t) = mk_val (Var (s,inst)) (Ty.allsubst g inst t) 

  module T = Ty
  let iip = T.parr T.int (T.parr T.int T.prop)
  let iii = T.parr T.int (T.parr T.int T.int)
  let ppp = T.parr T.prop (T.parr T.prop T.prop)
  let pre_defvar s t = 
    var (get_predef_var s) Inst.empty (T.Generalize.empty,t) 
  let svar s t = var s Inst.empty (T.Generalize.empty,t) 
  let le t1 t2 loc = appi (pre_defvar "<=" iip loc) t1 t2 loc
  let and_ t1 t2 loc = appi (pre_defvar "/\\" ppp loc) t1 t2 loc
  let impl t1 t2 loc = 
    appi (pre_defvar "->" ppp loc) t1 t2 loc
  let encl lower i upper loc = and_ (le lower i loc) (le i upper loc) loc
  let plam x t e loc = mk_val (PureFun (x,t,e)) (T.parr t e.t) loc
  let efflam x eff e = plam x (T.map eff) e
  let lam x t p e q = mk_val (Lam (x,t,p,e,q)) (T.arrow t e.t e.e)
  let ptrue_ loc = mk_val (Const (Const.Ptrue)) T.prop loc
  let plus t1 t2 loc = appi (pre_defvar "+" iii loc) t1 t2 loc
  let one = mk_val (Const (Const.Int 1)) T.int 
  let succ t loc = plus t (one loc) loc
  let let_ g e1 x e2 r = mk (Let (g,e1,x,e2,r)) e2.t (Effect.union e1.e e2.e)

  let letreg l e = mk (LetReg (l,e)) e.t (Effect.rremove l e.e)
  let ite e1 e2 e3 = 
    mk (Ite (e1,e2,e3)) e2.t (Effect.union e1.e (Effect.union e2.e e3.e))

  let typedef g t v e = mk (TypeDef (g,t,v,e)) e.t e.e

  let applist l loc = 
    match l with
    | [] | [ _ ] -> failwith "not enough arguments given"
    | a::b::rest ->
        List.fold_left (fun acc x -> app acc x loc) (app a b loc) rest

  let rec is_value = function
    | Const _ | Var _ | Lam _ | PureFun _ | Axiom _ | Logic _ | Quant _ -> true
    | Let _ | Ite _ | For _ | LetReg _ | Param _ | TypeDef _ | Annot _ -> false
    | App (t1,t2,_,_) -> 
        match t1.t with
        | T.C (T.PureArr _) -> true
        | _ -> false
  and is_value_node x = is_value x.v

  let squant k x t f loc = mk (Quant (k,x,t,f)) f.t f.e loc
  let sforall x = squant C.FA x
  let quant ?s k t f loc = 
    let v = 
      match s with 
      | None -> Var.new_anon () 
      | Some s -> Var.from_string s in
    let tv = svar v t loc in
    squant k v t (f tv) loc

  let forall ?s t f loc = quant ?s C.FA t f loc
  let effFA ?s e f loc = forall ?s (Ty.map e) f loc
      
end

module ParseT = struct
  type t = (unit,unit,unit) t'
  let nothing fmt () = ()
  let print fmt t = print nothing nothing nothing fmt t
  let mk v loc = { v = v; t = (); e = (); loc = loc }
  let pure_lam x t e = mk (PureFun (x,t,e))
  let annot e t = mk (Annot (e,t)) 
end

let concat t1 t2 =
  let rec aux' = function
    | Const Const.Void -> t2.v
    | Let (g,t1,x,t2,r) -> Let (g,t1,x,aux t2,r)
    | TypeDef (g,t,x,t2) -> TypeDef (g,t,x,aux t2)
    | _ -> assert false 
  and aux t = { t with v = aux' t.v } in
  aux t1
