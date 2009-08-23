module U = Unify
module C = Const
module G = Ty.Generalize

type ('a,'b,'c) t'' =
  | Const of Const.t
  | Var of Name.t * ('a,'b,'c) Inst.t
  | App of ('a,'b,'c) t' * ('a,'b,'c) t' * [`Infix | `Prefix ] * Name.t list
  | Lam of 
      Name.t * Ty.t * ('a,'b,'c) pre * ('a,'b,'c) t' * ('a,'b,'c) post 
  | Let of G.t * ('a,'b,'c) t' * ('a,'b,'c) t' Name.bind * isrec
  | PureFun of Ty.t * ('a,'b,'c) t' Name.bind
  | Ite of ('a,'b,'c) t' * ('a,'b,'c) t' * ('a,'b,'c) t'
  | Axiom of ('a,'b,'c) t'
  | Logic of Ty.t
  | Annot of ('a,'b,'c) t' * Ty.t
  | TypeDef of G.t * Ty.t option * Name.t * ('a,'b,'c) t'
  | Quant of [`FA | `EX ] * Ty.t * ('a,'b,'c) t' Name.bind
  | Param of Ty.t * NEffect.t
  | Gen of G.t *  ('a,'b,'c) t'
  | For of Name.t * ('a,'b,'c) pre * Name.t * Name.t * Name.t * ('a,'b,'c) t'
  | LetReg of Name.t list * ('a,'b,'c) t'
and ('a,'b,'c) t' = { v :('a,'b,'c)  t'' ; t : 'a ; e : 'c; loc : Loc.loc }
and ('a,'b,'c) post' = 
  | PNone
  | PPlain of ('a,'b,'c) t'
  | PResult of Name.t * ('a,'b,'c) t'
and ('a,'b,'c) pre = Name.t * ('a,'b,'c) t' option
and ('a,'b,'c) post = Name.t * Name.t * ('a,'b,'c) post'
and isrec = Rec of Ty.t | NoRec


open Myformat

let is_compound = function
  | Const _ | Var _ | Lam _ | PureFun _ | Annot _-> false
  | App _ | Let _ | Ite _ | Axiom _ | Logic _ | TypeDef _
  | Quant _ | Param _ | For _ | LetReg _ | Gen _ -> true
let is_compound_node t = is_compound t.v

let print pra prb prc fmt t = 
  let rec print' fmt = function
    | Const c -> Const.print fmt c
    | Var (v,i) -> 
        if Inst.is_empty i then Name.print fmt v
        else fprintf fmt "%a %a" Name.print v (Inst.print pra prb prc) i
    | App ({v = App ({ v = Var(v,_)},t1,_,_)},t2,`Infix,_) -> 
        fprintf fmt "@[%a@ %a@ %a@]" with_paren t1 Name.print v with_paren t2
    | App (t1,t2,_,cap) ->
          fprintf fmt "@[%a%a@ %a@]" print t1 maycap cap with_paren t2
    | Lam (x,t,p,e,q) -> 
        fprintf fmt "@[(λ(%a:%a)@ -->@ %a@ %a@ %a)@]" Name.print x 
          Ty.print t pre p print e post q
    | PureFun (t,(_,x,e)) ->
        fprintf fmt "@[(λ(%a:%a)@ ->@ %a)@]" Name.print x Ty.print t print e
    | Let (g,e1,(_,x,e2),r) -> 
        fprintf fmt "@[let@ %a%a %a=@[@ %a@]@ in@ %a@]" 
          prrec r Name.print x G.print g print e1 print e2
    | Ite (e1,e2,e3) ->
        fprintf fmt "@[if %a then %a else %a@]" print e1 print e2 print e3
    | Axiom e -> fprintf fmt "axiom %a" print e
    | Logic t -> fprintf fmt "logic %a" Ty.print t
    | TypeDef (g,t,x,e) -> 
        fprintf fmt "type %a%a =@ %a in@ %a" 
          Name.print x G.print g (opt_print Ty.print) t print e
    | Quant (k,t,(_,x,e)) ->
        fprintf fmt "@[%a (%a:%a).@ %a@]" C.quant k Name.print x Ty.print t print e
    | Param (t,e) -> fprintf fmt "param(%a,%a)" Ty.print t NEffect.print e
    | For (dir,inv,_,st,en,t) ->
        fprintf fmt "%a (%a) %a %a (%a)" 
          Name.print dir pre inv Name.print st Name.print en print t
    | Annot (e,t) -> fprintf fmt "(%a : %a)" print e Ty.print t
    | Gen (g,t) -> 
        fprintf fmt "forall %a. %a" G.print g print t
    | LetReg (v,t) -> 
        fprintf fmt "@[letregion %a in@ %a@]" 
          (print_list space Name.print) v print t
      
  and print fmt t = print' fmt t.v
  and pre fmt (_,x) = 
    match x with
    | None -> ()
    | Some x -> fprintf fmt "{%a}" print x
  and post fmt (_,_,x) = 
    match x with
    | PNone -> ()
    | PPlain f -> fprintf fmt "{%a}" print f
    | PResult (r,f) -> fprintf fmt "{ %a : %a}" Name.print r print f
  and prrec fmt = function
    | NoRec -> ()
    | Rec t -> fprintf fmt "rec(%a) " Ty.print t
  and maycap fmt = function
    | [] -> ()
    | l -> fprintf fmt "{%a}" (print_list space Name.print) l
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
  let lam_anon t e p = lam (Name.new_anon ()) t e p

  let print fmt t = print U.print_node U.prvar U.preff fmt t

end

module Recon = struct
  type t = (Ty.t, Name.t, NEffect.t) t'
  let print fmt t = print Ty.print Name.print NEffect.print fmt t

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t loc = { v = v; t = t; e = NEffect.empty; loc = loc }

  let app ?(kind=`Prefix) ?(cap=[]) t1 t2 loc = 
(*     Format.printf "termapp: %a and %a@." print t1 print t2; *)
    let t = Ty.result t1.t and e = Ty.latent_effect t1.t in
    mk (App (t1,t2,kind,cap)) t (NEffect.union t1.e (NEffect.union t2.e e)) loc


  let app2 t t1 t2 loc = app (app t t1 loc) t2 loc
  let appi t t1 t2 loc = app ~kind:`Infix (app t t1 loc) t2 loc
  let allapp t1 t2 kind cap loc = app ~kind ~cap t1 t2 loc
  let var s inst (g,t) = 
(*
    Format.printf "%a : (%a,%a) -> %a@." Name.print s Ty.Generalize.print g Ty.print
    t (Inst.print Ty.print Name.print NEffect.print) inst;
*)
    mk_val (Var (s,inst)) (Ty.allsubst g inst t) 

  module T = Ty
  let v = T.var

  let pre_defvar s inst = 
    let v,g,t = Ty.get_predef_var s in
    var v inst (g,t) 

  let spre_defvar s  = pre_defvar s Inst.empty

  open Const

  let ptrue_ loc = mk_val (Const (Ptrue)) T.prop loc
  let btrue_ loc = mk_val (Const (Btrue)) T.bool loc
  let bfalse_ loc = mk_val (Const (Bfalse)) T.bool loc

  let svar s t = var s Inst.empty (G.empty,t) 
  let le t1 t2 loc = appi (spre_defvar "<=" loc) t1 t2 loc
  let and_ t1 t2 loc = 
    match t1.v,t2.v with
    | Const Ptrue, _ -> t2
    | _, Const Ptrue -> t1
    | Const Pfalse, _ -> t1
    | _, Const Pfalse -> t2
    | _ -> appi (spre_defvar "/\\" loc) t1 t2 loc

  let impl t1 t2 loc = 
    match t1.v,t2.v with
    | Const Ptrue, _ -> t2
    | _, Const Ptrue -> t2
    | Const Pfalse, _ -> ptrue_ loc
    | _ -> appi (spre_defvar "->" loc) t1 t2 loc

  let eq t1 t2 loc = 
    appi (pre_defvar "=" ([t1.t],[],[]) loc) t1 t2 loc

  let pre t loc = 
    match t.t with
    | T.C (T.Tuple (t1,t2)) -> app (pre_defvar "fst" ([t1;t2],[],[]) loc) t loc
    | _ -> assert false

  let post t loc = 
    match t.t with
    | T.C (T.Tuple (t1,t2)) -> app (pre_defvar "snd" ([t1;t2],[],[]) loc) t loc
    | _ -> assert false

  let encl lower i upper loc = and_ (le lower i loc) (le i upper loc) loc
  let plam x t e loc = 
    mk_val (PureFun (t,Name.close_bind x e)) (T.parr t e.t) loc
  let efflam x eff e = plam x (T.map eff) e
  let lam x t p e q = mk_val (Lam (x,t,p,e,q)) (T.arrow t e.t e.e)
  let plus t1 t2 loc = appi (spre_defvar "+" loc) t1 t2 loc
  let one = mk_val (Const (Int Big_int.unit_big_int)) T.int 
  let succ t loc = plus t (one loc) loc
  let let_ g e1 x e2 r = 
    mk (Let (g, e1,Name.close_bind x e2,r)) e2.t (NEffect.union e1.e e2.e)

  let axiom e = mk (Axiom e) T.prop e.e
  let logic t = mk (Logic t) t NEffect.empty

  let mk_tuple t1 t2 loc = 
    appi (pre_defvar "," ([t1.t;t2.t],[],[]) loc) t1 t2 loc


  let letreg l e = mk (LetReg (l,e)) e.t (NEffect.rremove l e.e)
  let ite e1 e2 e3 = 
    mk (Ite (e1,e2,e3)) e2.t (NEffect.union e1.e (NEffect.union e2.e e3.e))

  let typedef g t v e = mk (TypeDef (g,t,v,e)) e.t e.e

  let applist l loc = 
    match l with
    | [] | [ _ ] -> failwith "not enough arguments given"
    | a::b::rest ->
        List.fold_left (fun acc x -> app acc x loc) (app a b loc) rest
  let andlist l loc = 
    match l with
    | [] | [ _ ] -> failwith "not enough arguments given"
    | a::b::rest ->
        List.fold_left (fun acc x -> and_ acc x loc) (and_ a b loc) rest

  let rec is_value = function
    | Const _ | Var _ | Lam _ | PureFun _ | Axiom _ | Logic _ | Quant _ -> true
    | Let _ | Ite _ | For _ | LetReg _ | Param _ | TypeDef _ 
    | Annot _ | Gen _ -> false
    | App (t1,_,_,_) -> 
        match t1.t with
        | T.C (T.PureArr _) -> true
        | _ -> false
  and is_value_node x = is_value x.v

  let squant k x t f loc = 
    match f.v with
    | Const Ptrue -> f
    | _ -> mk (Quant (k,t,Name.close_bind x f)) f.t f.e loc

  let gen g e l = 
    match e.v with
    | Const Ptrue -> e
    | _ -> mk (Gen (g, e)) e.t e.e l

  let rgen rl e = gen ([],rl,[]) e


  let sforall x = squant `FA x
  let quant ?s k t f loc = 
    let v = 
      match s with 
      | None -> Name.new_anon () 
      | Some s -> Name.from_string s in
    let tv = svar v t loc in
    squant k v t (f tv) loc

  let forall ?s t f loc = quant ?s `FA t f loc
  let effFA ?s e f loc = forall ?s (Ty.map e) f loc
  let plamho ?s t f loc = 
    let v = 
      match s with 
      | None -> Name.new_anon () 
      | Some s -> Name.from_string s in
    let tv = svar v t loc in
    plam v t (f tv) loc

  let efflamho ?s e f loc = plamho ?s (Ty.map e) f loc

  let rec is_param e = 
    match e.v with
    | Param _ -> true
    | Lam (_,_,_,e,_) -> is_param e
    | PureFun (_,(_,_,e)) -> is_param e
    | _ -> false

  let domain t = 
    match t.t with
    | Ty.C Ty.Map e -> e
    | _ -> assert false

  let combine t1 t2 l = 
    app2 (pre_defvar "combine" ([],[],[domain t1;domain t2]) l) t1 t2 l

  let restrict eff t l =
    app (pre_defvar "restrict" ([],[],[domain t; eff]) l) t l


end

module ParseT = struct
  type t = (unit,unit,unit) t'
  let nothing _ () = ()
  let print fmt t = print nothing nothing nothing fmt t
  let mk v loc = { v = v; t = (); e = (); loc = loc }
  let pure_lam x t e = mk (PureFun (t, Name.close_bind x e))
  let annot e t = mk (Annot (e,t)) 
end

let concat t1 t2 =
  let rec aux' = function
    | Const Const.Void -> t2.v
    | Let (g,e1,(_,x,t2),r) -> Let (g,e1, Name.close_bind x (aux t2), r)
    | TypeDef (g,t,x,t2) -> TypeDef (g,t,x,aux t2)
    | _ -> assert false 
  and aux t = { t with v = aux' t.v } in
  aux t1

let map ~varfun ~varbindfun f = 
  let rec aux' = function
    | (Const _ | Logic _ | Param _ ) as t -> t
    | Var (v,i) -> varfun v i
    | App (t1,t2,p,_) -> App (aux t1, aux t2, p, [])
    | Lam _ | Annot _ | For _ | LetReg _ -> assert false
    | Let (g,e1,b,r) -> Let (g,aux e1,varbindfun b, r)
    | PureFun (t,b) -> PureFun (t, varbindfun b)
    | Ite (e1,e2,e3) -> Ite (aux e1, aux e2, aux e3)
    | Axiom e -> Axiom (aux e)
    | TypeDef (g,t,x,e) -> TypeDef (g,t,x,aux e)
    | Quant (k,t,b) -> Quant (k,t,varbindfun b)
    | Gen (g,e) -> Gen (g,aux e)
  and aux t = {t with v = aux' t.v} in
  aux f

let refresh s t =
  map ~varfun:(fun x i -> Var (Name.refresh s x, i))
    ~varbindfun:(Name.refresh_bind s) t
