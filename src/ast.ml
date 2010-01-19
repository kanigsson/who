module U = Unify
module C = Const
module G = Ty.Generalize
module PL = Predefined.Logic

type ('a,'b,'c) t'' =
  | Const of Const.t
  | Var of Name.t * ('a,'b,'c) Inst.t
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of ('a,'b,'c) t' * ('a,'b,'c) t' * [`Infix | `Prefix ] * Name.t list
  | Lam of 
      Name.t * Ty.t * Name.t list * ('a,'b,'c) pre * ('a,'b,'c) t' * ('a,'b,'c) post 
  | Let of G.t * ('a,'b,'c) t' * ('a,'b,'c) t' Name.bind * isrec
  | PureFun of Ty.t * ('a,'b,'c) t' Name.bind
  | Ite of ('a,'b,'c) t' * ('a,'b,'c) t' * ('a,'b,'c) t'
  | Annot of ('a,'b,'c) t' * Ty.t
  | Quant of [`FA | `EX ] * Ty.t * ('a,'b,'c) t' Name.bind
  | Param of Ty.t * Effect.t
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
and isrec = Ty.t Const.isrec

type ('a,'b,'c) decl = 
  | Logic of Name.t *  G.t * Ty.t
  | Formula of string * ('a,'b,'c) t' * [ `Proved | `Assumed ]
  | Section of string * Const.takeover list * ('a,'b,'c) decl list
  | TypeDef of G.t * Ty.t option * Name.t
  | Program of Name.t * G.t * ('a,'b,'c) t' * isrec
  | DLetReg of Name.t list 

type ('a,'b,'c) theory = ('a,'b,'c) decl list

let map ~varfun ~varbindfun ~tyfun ~rvarfun ~effectfun f = 
  let rec aux' = function
    | (Const _ ) as t -> t
    | Param (t,e) -> Param (tyfun t, effectfun e)
    | Var (v,i) -> varfun v (Inst.map tyfun rvarfun effectfun i)
    | App (t1,t2,p,cap) -> App (aux t1, aux t2, p, List.map rvarfun cap)
    | Annot (e,t) -> Annot (aux e, tyfun t)
    | Lam (x,t,cap,p,e,q) -> 
        Lam (x,tyfun t, List.map rvarfun cap, pre p, aux e, post q)
    | LetReg (l,e) -> LetReg (l,aux e)
    | For _ -> assert false
    | Let (g,e1,b,r) -> Let (g,aux e1,varbindfun b, r)
    | PureFun (t,b) -> PureFun (tyfun t, varbindfun b)
    | Ite (e1,e2,e3) -> Ite (aux e1, aux e2, aux e3)
    | Quant (k,t,b) -> Quant (k,tyfun t,varbindfun b)
    | Gen (g,e) -> Gen (g,aux e)
  and pre (x,o) = (x, Misc.opt_map aux o)
  and post (x,y,f) = 
    let f = match f with
    | PNone -> PNone
    | PPlain f -> PPlain (aux f)
    | PResult (r,f) -> PResult (r,aux f) in
    x, y, f
  and aux t = {t with v = aux' t.v; t = tyfun t.t} in
  aux f

let refresh s t =
  map ~varfun:(fun x i -> Var (Name.refresh s x, i))
    ~varbindfun:(Name.refresh_bind s) 
    ~tyfun:Misc.id 
    ~rvarfun:Misc.id
    ~effectfun:Misc.id t

let vopen = Name.open_bind refresh
let close = Name.close_bind
let sopen = Name.sopen refresh
let vopen_with x = Name.open_with refresh x


let rec equal' a b =
  match a, b with
  | Const c1, Const c2 -> Const.compare c1 c2 = 0
  | Var (v1,i1), Var (v2,i2) ->
      Name.equal v1 v2 && 
      Inst.equal Ty.equal Name.equal Effect.equal i1 i2
  | App (a1,b1,_,_), App (a2,b2,_,_) -> equal a1 a2 && equal b1 b2
  | Gen (g1,t1), Gen (g2,t2) ->
      G.equal g1 g2 && equal t1 t2
  | Ite (a1,b1,c1), Ite (a2,b2,c2) -> equal a1 a2 && equal b1 b2 && equal c1 c2
  | Let (g1,ea1,b1,_), Let (g2,ea2,b2,_) ->
      G.equal g1 g2 && equal ea1 ea2 && bind_equal b1 b2
  | PureFun (t1,b1), PureFun (t2,b2) -> Ty.equal t1 t2 && bind_equal b1 b2
  | Quant (k1,t1,b1), Quant (k2,t2,b2) ->
      k1 = k2 && Ty.equal t1 t2 && bind_equal b1 b2
  | For _, _ | LetReg _, _ | Annot _, _ | Param _, _  
  | Lam _, _ -> assert false
  | _, _ -> false
and bind_equal b1 b2 = 
  (let x,eb1 = vopen b1 in
   let eb2 = vopen_with x b2 in
   equal eb1 eb2)

and equal a b = equal' a.v b.v

module Print = struct
  open Myformat

  let is_compound = function
    | Const _ | Var _ | Lam _ | PureFun _ | Annot _-> false
    | App _ | Let _ | Ite _
    | Quant _ | Param _ | For _ | LetReg _ | Gen _ -> true
  let is_compound_node t = is_compound t.v

  type sup = [ `Coq | `Who | `Pangoline ]
  let name_print ?(kind : sup =`Who) fmt x = 
    match kind with
    | `Pangoline -> 
        begin try 
          let s = Name.M.find x PL.pangoline_map in
          pp_print_string fmt s
        with Not_found -> Name.print fmt x end
    | `Coq | `Who -> Name.print fmt x

  let maycaplist fmt l = 
    if l = [] then ()
    else fprintf fmt "cap %a" (print_list space Name.print) l

  let prrec fmt = function
    | Const.NoRec -> ()
    | Const.Rec t -> fprintf fmt "rec(%a) " Ty.print t
    | Const.LogicDef -> fprintf fmt "logic " 

  let lname s fmt l = 
    if l = [] then () else
    fprintf fmt "(%a :@ %s)" (print_list space Name.print) l s

  (* TODO factorize the different branches *)
  let term ?(kind : sup =`Who) pra prb prc open_ fmt t = 
    let typrint = Ty.gen_print kind in
    let rec print' ext fmt = function
      | Const c -> Const.print kind fmt c
      | App ({v = App ({ v = Var(v,i)},t1,_,_)},t2,`Infix,_) -> 
          fprintf fmt "@[%a@ %a%a@ %a@]" with_paren t1 (name_print ~kind) v 
            (Inst.print ~kind ~intype:false pra prb prc) i with_paren t2
      | App (t1,t2,_,cap) ->
            fprintf fmt "@[%a%a@ %a@]" print t1 maycap cap with_paren t2
      | Ite (e1,e2,e3) ->
          fprintf fmt "@[if %a then@ %a else@ %a@]" print e1 print e2 print e3
      | PureFun (t,b) ->
          let x,e = open_ b in
          fprintf fmt "@[(fun %a@ %a@ %a)@]" binder (x,t) 
            Const.funsep kind print e
      | Let (g,e1,b,r) -> 
          let x,e2 = open_ b in
          if ext then
            fprintf fmt "@[let@ %a%a %a=@[@ %a@]@]@ @,%a" 
            prrec r Name.print x G.print g print e1 (extprint ext) e2
          else
          fprintf fmt "@[let@ %a%a %a=@[@ %a@]@ in@ %a@]" 
            prrec r Name.print x G.print g print e1 (extprint ext) e2
      | Var (v,i) -> 
          begin match kind with
          | `Who | `Pangoline ->
              let pr fmt () =
                if Inst.is_empty i then (name_print ~kind) fmt v 
                else fprintf fmt "%a %a" (name_print ~kind) v 
                  (Inst.print ~kind ~intype:false pra prb prc) i
              in 
              if Name.S.mem v PL.infix_set then Myformat.paren pr fmt ()
              else pr fmt ()
          | `Coq -> Name.print fmt v
          end
      | Annot (e,t) -> fprintf fmt "(%a : %a)" print e typrint t
      | Quant (k,t,b) ->
          let x,e = open_ b in
          let bind = if k = `FA then binder else binder' false in
          fprintf fmt "@[%a %a%a@ %a@]" C.quant k bind (x,t) 
            Const.quantsep kind print e
      | Gen ((tl,_,_) as g,t) -> 
          if G.is_empty g then print fmt t else
            begin match kind with
            | `Coq -> 
                fprintf fmt "forall@ %a@,@ %a " (lname "Type") tl print t
            | `Pangoline  -> 
                fprintf fmt "forall type %a. %a" (print_list space Name.print) tl
                  print t
            | `Who -> 
                fprintf fmt "forall %a%a %a" G.print g Const.quantsep kind print t
            end
      (* specific to Who, will not be printed in backends *)
      | Param (t,e) -> 
          fprintf fmt "parameter(%a,%a)" 
            typrint t Effect.print e
      | For (dir,inv,_,st,en,t) ->
          fprintf fmt "%a (%a) %a %a (%a)" 
            Name.print dir pre inv Name.print st Name.print en print t
      | LetReg (v,t) -> 
          fprintf fmt "@[letregion %a in@ %a@]" 
            (print_list space Name.print) v print t
      | Lam (x,t,cap,p,e,q) -> 
          fprintf fmt "@[(fun %a@ ->%a@ %a@ %a@ %a)@]" 
            binder (x,t) maycaplist cap pre p print e post q
        
    and print fmt t = print' false fmt t.v
    and extprint ext fmt t = 
      if ext then 
        if t.v = Const Const.Void then () 
        else print' true fmt t.v 
      else print fmt t
    and binder' par = 
      let p fmt (x,t) = fprintf fmt "%a:%a" 
        Name.print x typrint t in
      if par then paren p else p
    and binder fmt b = binder' true fmt b
    and pre fmt (_,x) = 
      match x with
      | None -> ()
      | Some x -> fprintf fmt "{%a}" print x
    and post fmt (_,_,x) = 
      match x with
      | PNone -> ()
      | PPlain f -> fprintf fmt "{%a}" print f
      | PResult (r,f) -> fprintf fmt "{ %a : %a}" Name.print r print f
    and maycap fmt = function
      | [] -> ()
      | l -> fprintf fmt "{%a}" (print_list space Name.print) l
    and with_paren fmt x = 
      if is_compound_node x then paren print fmt x else print fmt x in
    extprint true fmt t

  let decl ?(kind=`Who) pra prb prc open_ fmt d = 
    let typrint = Ty.gen_print kind in
    let term = term ~kind pra prb prc open_ in
    let rec decl fmt d = 
      match d with
      | Logic (x,g,t) -> 
          fprintf fmt "@[<hov 2>logic %a %a : %a@]" 
            Name.print x G.print g typrint t
      | Formula (s,t,`Assumed) ->  
          fprintf fmt "@[<hov 2>axiom %s : %a@]" s term t
      | Formula (s,t,`Proved) ->  
          fprintf fmt "@[<hov 2>goal %s : %a@]" s term t
      | TypeDef (g,t,x) -> 
          begin match t with
          | None -> fprintf fmt "type %a%a" Name.print x G.print g
          | Some t -> 
              fprintf fmt "type %a%a =@ %a" Name.print x G.print g typrint t
          end
      | DLetReg l ->
          fprintf fmt "@[letregion %a@]" (print_list space Name.print) l
      | Section (s,cl,d) -> 
          fprintf fmt "@[<hov 2>section %s@, %a@, %a@] end" s
          (print_list newline Const.takeover) cl decl_list d
      | Program (x,g,t,r) ->
          fprintf fmt "@[<hov 2>let@ %a%a %a = %a @]" prrec r 
          Name.print x G.print g term t 
    and decl_list fmt d = print_list newline decl fmt d in
    decl fmt d

  let theory ?kind pra prb prc open_ fmt t = 
    print_list newline (decl ?kind pra prb prc open_) fmt t
end

module Infer = struct
  type t = (U.node, U.rnode, U.effect) t'
  type pre' = (U.node, U.rnode, U.effect) pre
  type th' = (U.node, U.rnode, U.effect) theory
  type theory = th'

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t = mk v t U.eff_empty
  let const c = mk_val (Const c) (U.const (Const.type_of_constant c))
  let print fmt t = 
    Print.term ~kind:`Who U.print_node U.prvar U.preff
      (fun (_,x,e) -> x,e) fmt t

  let print_theory fmt t = 
    Print.theory ~kind:`Who U.print_node U.prvar U.preff
      (fun (_,x,e) -> x,e) fmt t

end

module N = Name

let destruct_app' = function
  | App (f1,f2,_,_) -> Some (f1,f2)
  | _ -> None

let destruct_app2 = function
  | App ({v = App (f1,f2,_,_)},f3,_,_) -> Some (f1,f2,f3)
  | _ -> None

let destruct_app2_var' x = 
  match destruct_app2 x with
  | Some ({v = Var (v,g)},f1,f2) -> Some (v,g,f1,f2)
  | _ -> None

let destruct_app2_var x = destruct_app2_var' x.v
let destruct_app x = destruct_app' x.v

let destruct_varname x = 
  match x.v with
  | Var (v, tl) -> Some (v,tl)
  | _ -> None

let open_close_map ~varfun ~tyfun ~rvarfun ~effectfun t =
  let rec aux t = 
    map ~varfun 
      ~varbindfun:(fun b -> let x,f = vopen b in close x (aux f))
      ~tyfun ~rvarfun ~effectfun t
  in
  aux t


module Recon = struct
  type t = (Ty.t, Name.t, Effect.t) t'
  type th = (Ty.t, Name.t, Effect.t) theory
  type decl' = (Ty.t, Name.t, Effect.t) decl
  type inst = (Ty.t, Name.t, Effect.t) Inst.t
  type theory = th
  type decl = decl'

  exception Error of string * Loc.loc

  let error loc s = 
    Myformat.ksprintf (fun s -> raise (Error (s,loc))) s

  let tsubst tvl tl e =
    open_close_map ~varfun:(fun v i -> Var (v,i)) 
                   ~tyfun:(Ty.tlsubst tvl tl) 
                   ~rvarfun:Misc.id
                   ~effectfun:Misc.id
                   e

  let rsubst rvl rl e = 
    open_close_map ~varfun:(fun v i -> Var (v,i)) 
                   ~tyfun:(Ty.rlsubst rvl rl) 
                   ~rvarfun:(Ty.rsubst rvl rl)
                   ~effectfun:(Effect.rmap (Ty.rsubst rvl rl))
                   e

  let esubst evl el e =
    open_close_map ~varfun:(fun v i -> Var (v,i))
      ~tyfun:(Ty.elsubst evl el)
      ~rvarfun:Misc.id
      ~effectfun:(Effect.lsubst evl el) e

  let allsubst ((tvl,rvl,evl) : G.t) ((tl,rl,el) : inst)  t = 
    esubst evl el (rsubst rvl rl (tsubst tvl tl t))

  let gen_print kind fmt t = 
    Print.term ~kind (Ty.gen_print kind) Name.print Effect.print sopen fmt t
  let coq_print fmt t = gen_print `Coq fmt t
  let print fmt t = gen_print `Who fmt t

  let print_decl =
    Print.decl ~kind:`Who (Ty.gen_print `Who) Name.print Effect.print sopen

  let print_theory = 
    Print.theory ~kind:`Who (Ty.gen_print `Who) Name.print Effect.print sopen

  let print' fmt t = 
    print fmt {v = t; t = Ty.unit; e = Effect.empty; loc = Loc.dummy }

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t loc = { v = v; t = t; e = Effect.empty; loc = loc }

  module PT = Ty.Predef
  let ptrue_ loc = mk_val (Const Const.Ptrue) Ty.prop loc
  let pfalse_ loc = mk_val (Const Const.Pfalse) Ty.prop loc
  let void loc = mk_val (Const Const.Void) Ty.unit loc

  let const c = 
    mk_val (Const c) (Ty.const (Const.type_of_constant c))

  let mempty = mk_val (Var (PL.empty_var, Inst.empty)) Ty.emptymap
  let btrue_ = mk_val (Var (PL.btrue_var, Inst.empty)) Ty.bool 
  let bfalse_ = mk_val (Var (PL.bfalse_var, Inst.empty)) Ty.bool

  let var s inst (g,t) = 
    let nt = (Ty.allsubst g inst t) in
    if Ty.equal nt Ty.unit then void 
    else if Ty.equal nt Ty.emptymap then mempty
    else mk_val (Var (s,inst)) nt

  let var_i s inst t = mk_val (Var (s,inst)) t
  let svar s t = var s Inst.empty (G.empty, t)

  module Predef = struct
    let neg_t = svar PL.not_var PT.prop_2

    let leb_t = svar PL.leb_var PT.iib
    let ltb_t = svar PL.ltb_var PT.iib
    let gtb_t = svar PL.gtb_var PT.iib
    let geb_t = svar PL.geb_var PT.iib
    let eqb_t i = var PL.eqb_var i PT.aab
    let neqb_t i = var PL.neqb_var i PT.aab
    let andb_t = svar PL.andb_var PT.bool_3
    let orb_t = svar PL.orb_var PT.bool_3

    let le_t = svar PL.le_var PT.iip
    let lt_t = svar PL.lt_var PT.iip
    let ge_t = svar PL.ge_var PT.iip
    let gt_t = svar PL.gt_var PT.iip
    let neq_t i = var PL.neq_var i PT.aap
    let eq_t i = var PL.equal_var i PT.aap

    let and_t = svar PL.and_var PT.prop_3
    let or_t = svar PL.or_var PT.prop_3
    let impl_t = svar PL.impl_var PT.prop_3

    let tuple_t i = var PL.tuple_var i PT.mk_tuple
    let fst_t i = var PL.fst_var i PT.fst
    let snd_t i = var PL.snd_var i PT.snd

    let plus_t = svar PL.plus_var PT.int_3
    let minus_t = svar PL.minus_var PT.int_3

    let combine_t i = var PL.combine_var i PT.combine
    let restrict_t i = var PL.restrict_var i PT.restrict
    let get_t i = var PL.get_var i PT.get
  end

  module P = Predef

  let true_or e v = 
    match e.v with
    | Const Const.Ptrue -> e
    | _ -> v

  let annot e t = true_or e (mk (Annot (e,t)) t e.e e.loc)

  let domain t = 
    match t.t with
    | Ty.C Ty.Map e -> e
    | _ -> assert false

  let let_ g e1 x e2 r l = 
    true_or e2 
      (mk (Let (g, e1,Name.close_bind x e2,r)) e2.t 
        (Effect.union e1.e e2.e) l)

  let plam x t e loc = 
    mk_val (PureFun (t,Name.close_bind x e)) (Ty.parr t e.t) loc

  let gen g e l = true_or e (mk (Gen (g, e)) e.t e.e l)

  let simple_app ?(kind=`Prefix) ?(cap=[]) t1 t2 l =
    let t = Ty.result t1.t and e = Ty.latent_effect t1.t in
    if not (Ty.equal (Ty.arg t1.t) t2.t) then begin
      Myformat.printf "type mismatch on application: function %a has type %a,
      and argument %a has type %a@." print t1 Ty.print t1.t 
      print t2 Ty.print t2.t ; invalid_arg "app" end
    else 
      mk (App (t1,t2,kind,cap)) t (Effect.union t1.e (Effect.union t2.e e)) l
  let simple_app2 ?kind t t1 t2 loc = 
    simple_app ?kind (simple_app t t1 loc) t2 loc
  let simple_appi t t1 t2 loc = simple_app2 ~kind:`Infix t t1 t2 loc

  let boolcmp_to_propcmp x = 
    let eq = Name.equal in
    match x with
    | x when eq x PL.leb_var -> fun _ -> P.le_t
    | x when eq x PL.ltb_var -> fun _ -> P.lt_t
    | x when eq x PL.geb_var -> fun _ -> P.ge_t
    | x when eq x PL.gtb_var -> fun _ -> P.gt_t
    | x when eq x PL.eqb_var -> P.eq_t
    | x when eq x PL.neqb_var -> P.neq_t
    | x when eq x PL.andb_var -> fun _ -> P.and_t
    | x when eq x PL.orb_var -> fun _ -> P.or_t
    | _ -> raise Exit

  let rec app ?kind ?cap t1 t2 l : t = 
(*     Myformat.printf "app: %a and %a@." print t1 print t2; *)
      try match t1.v with
      (* we are trying to build (λx.t) e, reduce to t[x|->e] *)
      | PureFun (_,l) ->
          let x, body = vopen l in
          subst x (fun _ -> t2) body
      (* double application, check if we are not in a simplification case *)
      | App (op,t1,_,_) ->
          begin match destruct_varname op with
          | Some (v,_) when Name.equal v PL.and_var -> and_ t1 t2 l
          | Some (v,_) when Name.equal v PL.impl_var -> impl t1 t2 l
          | Some (v,_) when Name.equal v PL.equal_var -> eq t1 t2 l
          | Some (v,_) when Name.equal v PL.combine_var -> combine t1 t2 l
          | _ -> raise Exit
          end
      | _ ->
      (* simple application *)
          match destruct_varname t1 with
          | Some (v,_) when Name.equal v PL.not_var -> neg t2 l
          | Some (v, _) when Name.equal v PL.fst_var -> pre t2 l
          | Some (v, _) when Name.equal v PL.snd_var -> post t2 l
          | Some (v, ([],[],[_;b])) when Name.equal v PL.restrict_var -> 
              restrict b t2 l
          | _ -> raise Exit
      with Exit -> simple_app ?kind ?cap t1 t2 l

  and app2 ?kind t t1 t2 loc = app ?kind (app t t1 loc) t2 loc
  and appi t t1 t2 loc = app2 ~kind:`Infix t t1 t2 loc
  and allapp t1 t2 kind cap loc = app ~kind ~cap t1 t2 loc
  and neg f l = 
    match f.v with
    | Const Const.Ptrue -> pfalse_ l
    | Const Const.Pfalse -> ptrue_ l
    | _ -> simple_app (P.neg_t l) f l

  and reduce_bool t l = 
    let rec aux t =
      match destruct_app2_var t with
      | Some (op, i, arg1, arg2) ->
          let v = boolcmp_to_propcmp op in
          let arg1, arg2 = 
            if Name.equal op PL.andb_var || Name.equal op PL.orb_var then 
              aux arg1, aux arg2
            else arg1, arg2 in
          appi (v i l) arg1 arg2 l
      | None -> raise Exit in
    aux t
  and rebuild_map ~varfun ~termfun t =
    (* this function is intended to be used with logic functions only *)
    let l = t.loc in
    let rec aux t = 
      let t = 
        match t.v with
        | Const _ -> t
        | Var (v,i) -> varfun v i t
        | App (t1,t2,p,cap) -> allapp (aux t1) (aux t2) p cap l
        | Annot (e,t) -> annot (aux e) t
        | Let (g,e1,b,r) -> 
            let x,f = vopen b in 
            let_ g (aux e1) x (aux f) r l
        | PureFun (t,b) -> 
            let x,f = vopen b in 
            plam x t (aux f) l
        | Quant (k,t,b) -> 
            let x,f = vopen b in 
            squant k x t (aux f) l
        | Ite (e1,e2,e3) -> ite ~logic:false (aux e1) (aux e2) (aux e3) l
        | Gen (g,e) -> gen g (aux e) l
        | For _ | LetReg _ | Param _ | Lam _  -> assert false in
      termfun t in
    aux t
  and impl h1 goal l = 
(*     Myformat.printf "impl: %a and %a@." print h1 print goal; *)
    try match destruct_app2_var h1 with
    | Some (v, _, ha, hb) when Name.equal v PL.and_var -> impl ha (impl hb goal l) l
    | _ ->
        match destruct_app2_var goal with
        | Some (v, _, h2, goal) when Name.equal v PL.impl_var ->
            begin match destruct_app2_var h1,destruct_app2_var h2 with
            | Some ( v, _,_, _), _ when Name.equal v PL.equal_var -> raise Exit
            | _, Some (v, _,_, _) when Name.equal v PL.equal_var -> 
                impl h2 (impl h1 goal l) l
            | _ -> raise Exit
            end
         | _ ->
             begin match h1.v,goal.v with
             | Const Const.Ptrue, _ -> goal
             | _, Const Const.Ptrue -> goal
             | Const Const.Pfalse, _ -> ptrue_ l
             | _, _ when equal h1 goal -> ptrue_ l
             | _ -> raise Exit
            end
    with Exit -> simple_appi (P.impl_t l) h1 goal l
  and ite ?(logic=true) e1 e2 e3 l = 
    let im b c = impl (eq e1 (b l) l) c l in
    if logic then and_ (im btrue_ e2) (im bfalse_ e3) l
    else
      mk (Ite (e1,e2,e3)) e2.t (Effect.union e1.e (Effect.union e2.e e3.e)) l
  and eq t1 t2 l = 
    if equal t1 t2 then ptrue_ l 
    else
      match t2.v with
      | Var (v, ([], [], [])) when 
         Name.equal v PL.btrue_var || Name.equal v PL.bfalse_var ->
          let f = reduce_bool t1 l in
          if Name.equal v PL.btrue_var then f else neg f l
      | _ -> simple_appi (P.eq_t ([t1.t],[],[]) l) t1 t2 l
  and and_ t1 t2 l = 
    match t1.v,t2.v with
    | Const Const.Ptrue, _ -> t2
    | _, Const Const.Ptrue -> t1
    | Const Const.Pfalse, _ -> t1
    | _, Const Const.Pfalse -> t2
    | _ -> simple_appi (P.and_t l) t1 t2 l
  and subst x v e =
(*     Myformat.printf "subst: %a@." Name.print x ; *)
    rebuild_map
      ~varfun:(fun z i def -> if Name.equal z x then v i else def)
      ~termfun:Misc.id e

  and polsubst g x v e = subst x (fun i -> allsubst g i v) e
  and squant k x t f loc = 
    if Ty.equal t Ty.unit || Ty.equal t Ty.emptymap then f 
    else (
      try match destruct_app2_var f with
      | Some (i, _, t1,f) when Name.equal i PL.impl_var ->
          begin match destruct_app2_var t1 with
          | Some (e, _,({v= Var(y,_)} as t1), ({v = Var (z,_)} as t2) ) 
            when Name.equal e PL.equal_var ->
              if Name.equal x y then subst x (fun _ -> t2) f
              else if Name.equal x z then subst z (fun _ -> t1) f
              else raise Exit
          | Some (e, _,{v= Var(y,_)}, def)
              when Name.equal e PL.equal_var ->
              if Name.equal x y then subst x (fun _ -> def) f else raise Exit
          | Some (e, _,def,{v = Var (y,_)})
              when Name.equal e PL.equal_var ->
              if Name.equal x y then subst x (fun _ -> def) f else raise Exit
          | _ -> 
              raise Exit
          end
      | _ -> raise Exit
      with Exit -> 
        true_or f (mk (Quant (k,t,Name.close_bind x f)) f.t f.e loc) )

  and pre t l = 
    match destruct_app2_var t with
    | Some (v,_,a,_) when Name.equal v PL.tuple_var -> a
    | _ -> 
        try 
          let t1, t2 = Ty.destr_tuple t.t in
          simple_app (P.fst_t ([t1;t2],[],[]) l) t l
        with Invalid_argument "Ty.destr_tuple" ->
          error t.loc "term %a is not of tuple type, but of type %a@." 
            print t Ty.print t.t


  and post t l = 
    match destruct_app2_var t with
    | Some (v,_,_,b) when Name.equal v PL.tuple_var -> b
    | _ -> 
        try
          let t1, t2 = Ty.destr_tuple t.t in
          simple_app (P.snd_t ([t1;t2],[],[]) l) t l
        with Invalid_argument "Ty.destr_tuple" ->
          error t.loc "term %a is not of tuple type, but of type %a@." 
            print t Ty.print t.t
  and combine t1 t2 l = 
    let d1 = domain t1 and d2 = domain t2 in
    let d1', d2', d3' = Effect.split d1 d2 in
    if Effect.is_empty d1' then t2
    else 
      match destruct_app2_var t1 with
      | Some (v,([],[],[e1;_;_]), _, db)
        when Name.equal v PL.combine_var && Effect.sub_effect e1 d2' -> 
          combine db t2 l
      | _  -> simple_app2 (P.combine_t ([],[],[d1';d2';d3']) l) t1 t2 l

  and restrict eff t l =
    let d = Effect.diff (domain t) eff in
    if Effect.is_empty d then t else
    try
      match destruct_app2_var t with
      | Some (v,([],[],[e1;_;e3]), m1, m2) 
        when Name.equal v PL.combine_var  ->
          if Effect.sub_effect eff e3 then restrict eff m2 l
          else if Effect.sub_effect eff e1 then restrict eff m1 l
          else raise Exit
      | _ -> raise Exit
    with Exit -> simple_app (P.restrict_t ([],[],[d; eff]) l) t l

    
  let svar s t = var s Inst.empty (G.empty,t) 
  let le t1 t2 loc = simple_appi (P.le_t loc) t1 t2 loc

  let encl lower i upper loc = and_ (le lower i loc) (le i upper loc) loc
  let efflam x eff e = plam x (Ty.map eff) e
  let lam x t p e q = 
    mk_val (Lam (x,t,[],p,e,q)) (Ty.arrow t e.t e.e)
  let caplam x t cap p e q = 
    mk_val (Lam (x,t,cap,p,e,q)) (Ty.caparrow t e.t e.e cap)
  let plus t1 t2 loc = appi (P.plus_t loc) t1 t2 loc
  let minus t1 t2 loc = appi (P.minus_t loc) t1 t2 loc
  let one = mk_val (Const (Const.Int Big_int.unit_big_int)) Ty.int 
  let succ t loc = plus t (one loc) loc
  let prev t loc = minus t (one loc) loc

  let param t e = mk (Param (t,e)) t e

  let mk_tuple t1 t2 loc = 
    appi (P.tuple_t ([t1.t;t2.t],[],[]) loc) t1 t2 loc


  let letreg l e = mk (LetReg (l,e)) e.t (Effect.rremove e.e l)

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
    | Const _ | Var _ | Lam _ | PureFun _ | Quant _ -> true
    | Let _ | Ite _ | For _ | LetReg _ | Param _
    | Annot _ | Gen _ -> false
    | App (t1,_,_,_) -> 
        match t1.t with
        | Ty.C (Ty.PureArr _) -> true
        | _ -> false
  and is_value_node x = is_value x.v

  let aquant k x t f loc = 
    match k with
    | `LAM -> plam x t f loc
    | (`FA | `EX) as k -> squant k x t f loc

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
    | Lam (_,_,_,_,e,_) -> is_param e
    | PureFun (_,(_,_,e)) -> is_param e
    | _ -> false

  let destruct_restrict' x = 
    match destruct_app' x with
    | Some ({v = Var (v,([],[],[e1;e2]))},map) when Name.equal v PL.restrict_var ->
        Some (map,e1,e2)
    | _ -> None

  let destruct_get' x = 
    match destruct_app2_var' x with
    | Some (v, ([t],[reg],[e]), r,map) when Name.equal v PL.get_var -> 
        Some (t,r,reg,Effect.radd e reg,map)
    | _ -> None

  let destruct_get x = destruct_get' x.v

  let get ref map l = 
    match ref.t with 
    | Ty.C (Ty.Ref (r,t)) ->
        let d = domain map in
        let d = Effect.rremove d [r] in
        simple_app2 (P.get_t ([t],[r],[d]) l) ref map l
    | _ -> assert false

  let rec decl_map ~varfun ~termfun ~declfun d : decl list =
    let d = 
      match d with
      | Logic _ | TypeDef _ | DLetReg _ -> d
      | Formula (s,t,k) -> Formula (s,rebuild_map ~varfun ~termfun t, k)
      | Section (s,cl,th) -> 
          Section (s,cl,theory_map ~varfun ~termfun ~declfun th)
      | Program (n,g,t,r) -> Program (n,g,rebuild_map ~varfun ~termfun t, r) in
    declfun d
  and theory_map ~varfun ~termfun ~declfun th = 
    List.flatten (List.map (decl_map ~varfun ~termfun ~declfun) th)

  let mk_formula n f k = 
    match f.v with
    | Const Const.Ptrue -> None
    | _ -> Some (Formula (n,f,k))

  let mk_goal n f = mk_formula n f `Proved

end

module ParseT = struct
  type t = (unit,unit, Effect.t) t'
  type theory' = (unit, unit, Effect.t) theory
  type theory = theory'

  let nothing _ _ = ()
  let print fmt t = 
    Print.term nothing nothing Effect.print (fun (_,x,e) -> x,e) fmt t
  let print_theory fmt t = 
    Print.theory nothing nothing Effect.print (fun (_,x,e) -> x,e) fmt t
  let mk v loc = { v = v; t = (); e = Effect.empty; loc = loc }
  let pure_lam x t e = mk (PureFun (t, Name.close_bind x e))
  let var ?(inst = []) v = mk (Var (v,([],[],inst)))
  let annot e t = mk (Annot (e,t))
  let gen g e = mk (Gen (g,e)) e.loc
  let ptrue l = mk (Const Const.Ptrue) l

  let app t1 t2 = mk (App (t1,t2,`Prefix, []))
end
