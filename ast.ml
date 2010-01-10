module U = Unify
module C = Const
module G = Ty.Generalize

type ('a,'b,'c) t'' =
  | Const of Const.t
  | Var of Name.t * ('a,'b,'c) Inst.t
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of ('a,'b,'c) t' * ('a,'b,'c) t' * [`Infix | `Prefix ] * Name.t list
  | Lam of 
      Name.t * Ty.t * Name.t list * ('a,'b,'c) pre * ('a,'b,'c) t' * ('a,'b,'c) post 
  (* boolean which describes if the let comes from the prelude or not *)  
  | Let of G.t * ('a,'b,'c) t' * ('a,'b,'c) t' Name.bind * isrec
  | PureFun of Ty.t * ('a,'b,'c) t' Name.bind
  | Ite of ('a,'b,'c) t' * ('a,'b,'c) t' * ('a,'b,'c) t'
  | Annot of ('a,'b,'c) t' * Ty.t
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

type ('a,'b,'c) decl = 
  | Logic of Name.t *  G.t * Ty.t
  | Axiom of string * ('a,'b,'c) t'
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
      Inst.equal Ty.equal Name.equal NEffect.equal i1 i2
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

  let maycaplist fmt l = 
    if l = [] then ()
    else fprintf fmt "cap %a" (print_list space Name.print) l

  let prrec fmt = function
    | NoRec -> ()
    | Rec t -> fprintf fmt "rec(%a) " Ty.print t
  (* TODO factorize the different branches *)
  let term ?(kind=`Who) pra prb prc open_ fmt t = 
    let typrint = Ty.gen_print kind in
    let rec print' ext fmt = function
      | Const c -> Const.print fmt c
      | App ({v = App ({ v = Var(v,i)},t1,_,_)},t2,`Infix,_) -> 
          fprintf fmt "@[%a@ %a%a@ %a@]" with_paren t1 Name.print v 
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
              if Inst.is_empty i then Name.print fmt v 
              else fprintf fmt "%a %a" Name.print v 
                (Inst.print ~kind ~intype:false pra prb prc) i
          | `Coq -> Name.print fmt v
          end
      | Annot (e,t) -> fprintf fmt "(%a : %a)" print e typrint t
      | Quant (k,t,b) ->
          let x,e = open_ b in
          let bind = if k = `FA then binder else binder' false in
          fprintf fmt "@[%a %a%a@ %a@]" C.quant k bind (x,t) 
            Const.quantsep kind print e
      | Gen (g,t) -> 
          fprintf fmt "forall %a%a %a" G.print g Const.quantsep kind print t
      (* specific to Who, will not be printed in backends *)
      | Param (t,e) -> 
          fprintf fmt "parameter(%a,%a)" 
            typrint t NEffect.print e
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
      | Axiom (s,t) ->  
          fprintf fmt "@[<hov 2>axiom %s : %a@]" s term t
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
  type t = (U.node, U.rnode, U.enode) t'
  type th' = (U.node, U.rnode, U.enode) theory
  type theory = th'

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t = mk v t (U.new_e ())
  let const c = mk_val (Const c) (U.const (Const.type_of_constant c))

  let lam x t p e q = 
    mk_val (Lam (x,U.to_ty t,[],p,e,q)) (U.arrow t e.t e.e [])
  let caplam x t cap p e q = 
    mk_val (Lam (x,U.to_ty t,cap,p,e,q)) (U.arrow t e.t e.e [])
(*   let plam x t e = mk_val (PureFun (x,t,e)) (U.parr t e.t) *)
  let lam_anon t e p = lam (Name.new_anon ()) t e p

  let print fmt t = 
    Print.term ~kind:`Who U.print_node U.prvar U.preff (fun (_,x,e) -> x,e) fmt t

  let print_theory fmt t = 
    Print.theory ~kind:`Who U.print_node U.prvar U.preff (fun (_,x,e) -> x,e) fmt t

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
  | Some ({v = Var ({Name.name = v},g)},f1,f2) -> Some (v,g,f1,f2)
  | _ -> None

let destruct_get' x = 
  match destruct_app2_var' x with
  | Some (Some "!!", ([t],[reg],[e]), r,map) -> 
      Some (t,r,reg,e,map)
  | _ -> None

let destruct_kget' x = 
  match destruct_app2_var' x with
  | Some (Some "kget", ([t],[reg],[]), ref,map) -> 
      Some (t,ref,reg,map)
  | _ -> None

let destruct_restrict' x = 
  match destruct_app' x with
  | Some ({v = Var ({Name.name = Some "restrict"},([],[],[e1;e2]))}, map) ->
      Some (map,e1,e2)
  | _ -> None

let destruct_krestrict' x = 
  match destruct_app' x with
  | Some ({v = Var ({Name.name = Some "krestrict"},([],[],[e1;e2]))}, map) ->
      Some (map,e1,e2)
  | _ -> None

let destruct_combine' x = 
  match destruct_app2_var' x with
  | Some (Some "combine",([],[],[e1;e2]), m1,m2) ->
      Some (m1,e1,m2,e2)
  | _ -> None

let destruct_kcombine' x = 
  match destruct_app2_var' x with
  | Some (Some "kcombine",([],[],[e1;e2]), m1,m2) ->
      Some (m1,e1,m2,e2)
  | _ -> None

let destruct_app2_var x = destruct_app2_var' x.v
let destruct_app x = destruct_app' x.v
let destruct_get x = destruct_get' x.v
let destruct_kget x = destruct_kget' x.v
let destruct_restrict x = destruct_restrict' x.v
let destruct_combine x = destruct_combine' x.v
let destruct_krestrict x = destruct_krestrict' x.v
let destruct_kcombine x = destruct_kcombine' x.v

let destruct_varname x = 
  match x.v with
  | Var ({ Name.name = Some v}, tl) -> Some (v,tl)
  | _ -> None

let open_close_map ~varfun ~tyfun ~rvarfun ~effectfun t =
  let rec aux t = 
    map ~varfun 
      ~varbindfun:(fun b -> let x,f = vopen b in close x (aux f))
      ~tyfun ~rvarfun ~effectfun t
  in
  aux t

let tsubst tvl tl e =
  open_close_map ~varfun:(fun v i -> Var (v,i)) 
                 ~tyfun:(Ty.tlsubst tvl tl) 
                 ~rvarfun:Misc.id
                 ~effectfun:Misc.id
                 e

let rsubst rvl rl e = 
(*
  Myformat.printf "rsubsting: [%a|->%a]@." Name.print_list rvl Name.print_list
  rl;
*)
  open_close_map ~varfun:(fun v i -> Var (v,i)) 
                 ~tyfun:(Ty.rlsubst rvl rl) 
                 ~rvarfun:(Ty.rsubst rvl rl)
                 ~effectfun:(NEffect.rmap (Ty.rsubst rvl rl))
                 e

let esubst evl el e =
  open_close_map ~varfun:(fun v i -> Var (v,i))
    ~tyfun:(Ty.elsubst evl el)
    ~rvarfun:Misc.id
    ~effectfun:(NEffect.lsubst evl el) e

module Recon = struct
  type t = (Ty.t, Name.t, NEffect.t) t'
  type th = (Ty.t, Name.t, NEffect.t) theory
  type theory = th


  let gen_print kind fmt t = 
    Print.term ~kind (Ty.gen_print kind) Name.print NEffect.print sopen fmt t
  let coq_print fmt t = gen_print `Coq fmt t
  let print fmt t = gen_print `Who fmt t

  let print_theory = 
    Print.theory ~kind:`Who (Ty.gen_print `Who) Name.print NEffect.print sopen

  let print' fmt t = 
    print fmt {v = t; t = Ty.unit; e = NEffect.empty; loc = Loc.dummy }

  let mk v t e loc = { v = v; t = t; e = e; loc = loc }
  let mk_val v t loc = { v = v; t = t; e = NEffect.empty; loc = loc }

  let ptrue_ loc = mk_val (Const Const.Ptrue) Ty.prop loc
  let pfalse_ loc = mk_val (Const Const.Pfalse) Ty.prop loc
  let btrue_ loc = mk_val (Const Const.Btrue) Ty.bool loc
  let bfalse_ loc = mk_val (Const Const.Bfalse) Ty.bool loc
  let void loc = mk_val (Const Const.Void) Ty.unit loc

  let true_or e v = 
    match e.v with
    | Const Const.Ptrue -> e
    | _ -> v

  let annot e t = true_or e (mk (Annot (e,t)) t e.e e.loc)

  let let_ g e1 x e2 r l = 
    true_or e2 
      (mk (Let (g, e1,Name.close_bind x e2,r)) e2.t 
        (NEffect.union e1.e e2.e) l)

  let plam x t e loc = 
    mk_val (PureFun (t,Name.close_bind x e)) (Ty.parr t e.t) loc

  let gen g e l = true_or e (mk (Gen (g, e)) e.t e.e l)

  let rec app ?(kind=`Prefix) ?(cap=[]) t1 t2 l = 
(*     Format.printf "termapp: %a and %a@." print t1 print t2; *)
    let t = Ty.result t1.t and e = Ty.latent_effect t1.t in
    if not (Ty.equal (Ty.arg t1.t) t2.t) then begin
      Myformat.printf "type mismatch on application: function %a has type %a,
      and argument %a has type %a@." print t1 Ty.print t1.t 
      print t2 Ty.print t2.t ; invalid_arg "app" end
    else 
      try match t1.v with
      (* we are trying to build (λx.t) e, reduce to t[x|->e] *)
      | PureFun (_,l) ->
          let x, body = vopen l in
          subst x (fun _ -> t2) body
      (* double application, check if we are not in a simplification case *)
      | App (op,t1,_,_) ->
          begin match destruct_varname op with
          (* simpl for /\ *)
          | Some ("/\\",_) ->
              begin match t1.v,t2.v with
              | Const Const.Ptrue, _ -> t2
              | _, Const Const.Ptrue -> t1
              | Const Const.Pfalse, _ -> t1
              | _, Const Const.Pfalse -> t2
              | _ -> raise Exit
              end
          (* simpl for -> *)
          | Some ("->",_) ->
              (* (a /\b) -> c ====>    a -> b -> b *)
              begin match destruct_app2_var t1 with
              | Some (Some "/\\", _, ha, hb) ->
                  impl ha (impl hb t2 l) l
              | _ ->
                  match destruct_app2_var t2 with
                  | Some (Some "->", _, t2, goal) ->
                      begin match destruct_app2_var t1,destruct_app2_var t2 with
                      | Some ( Some "=", _,_, _), _ -> raise Exit
                      | _, Some (Some "=", _,_, _) -> impl t2 (impl t1 goal l) l
                      | _ -> raise Exit
                      end
                  | _ ->
                      begin match t1.v,t2.v with
                      | Const Const.Ptrue, _ -> t2
                      | _, Const Const.Ptrue -> t2
                      | Const Const.Pfalse, _ -> ptrue_ l
                      | _, _ when equal t1 t2 -> ptrue_ l
                      | _ -> raise Exit
                      end
              end
          | Some ("=",_) ->
              if equal t1 t2 then ptrue_ l 
              else
                begin match t2.v with
                | (Const Const.Btrue | Const Const.Bfalse) as n ->
                    let f = reduce_bool t1 l in
                    if n = Const Const.Btrue then f else neg f l
                | _ -> raise Exit
                end
          | _ -> raise Exit
          end
      | _ ->
          match destruct_varname t1 with
          | Some ("~",_) -> 
              begin match t2.v with
              | Const Const.Ptrue -> pfalse_ l
              | Const Const.Pfalse -> ptrue_ l
              | _ -> raise Exit
              end
          | Some (("fst" | "pre" | "post" | "snd" as n),_) ->
              begin match destruct_app2_var t2 with
              | Some (Some ",",_,a,b) ->
                  if n = "fst" || n = "pre" then a 
                  else b
              | _ -> raise Exit
              end
          | _ -> raise Exit
      with Exit -> 
        mk (App (t1,t2,kind,cap)) t 
          (NEffect.union t1.e (NEffect.union t2.e e)) l

  and app2 ?kind t t1 t2 loc = app ?kind (app t t1 loc) t2 loc
  and appi t t1 t2 loc = app2 ~kind:`Infix t t1 t2 loc
  and allapp t1 t2 kind cap loc = app ~kind ~cap t1 t2 loc
  and var s inst (g,t) = 
(*
    Format.printf "%a : (%a,%a) -> %a@." Name.print s Ty.Generalize.print g Ty.print
    t (Inst.print Ty.print Name.print NEffect.print) inst;
*)
    let nt = (Ty.allsubst g inst t) in
    if Ty.equal nt Ty.unit then void 
    else if Ty.equal nt Ty.emptymap then mempty
    else mk_val (Var (s,inst)) nt

  and var_i s inst t =
    mk_val (Var (s,inst)) t

  and pre_defvar s inst = 
    let v,g,t = Ty.get_predef_var s in
    var v inst (g,t) 

  and spredef_var s  = pre_defvar s Inst.empty
  and mempty l = 
    let v,_,_ = Ty.get_predef_var "empty" in
    mk_val (Var (v,Inst.empty)) Ty.emptymap l

  and neg f l = app (spredef_var "~" l) f l

  and reduce_bool t loc = 
    let rec aux t =
      match destruct_app2_var t with
      | Some (op, g, arg1, arg2) ->
          let op' = 
            match op with
            | Some "<<=" -> "<="
            | Some "<<" -> "<"
            | Some ">>" -> ">"
            | Some ">>=" -> ">="
            | Some "==" -> "="
            | Some "!=" -> "<>"
            | Some "band" -> "/\\"
            | Some "bor" -> "\\/"
            | _ -> raise Exit
          in
          let f arg = if op' = "/\\" || op' = "\\/" then aux arg else arg in
          appi (pre_defvar op' g loc) (f arg1) (f arg2) loc
      | None -> raise Exit in
    aux t
  and rebuild_map ~varfun t =
    (* this function is intended to be used with logic functions only *)
    let l = t.loc in
    let rec aux t = match t.v with
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
    | _ -> assert false in
    aux t
  and impl h1 goal l = 
    try match destruct_app2_var h1 with
    | Some (Some "/\\", _, ha, hb) ->
        impl ha (impl hb goal l) l
    | _ -> raise Exit
    with Exit ->
      try match destruct_app2_var goal with
      | Some ( Some "->", _, h2,goal)  ->
          begin match destruct_app2_var h1, destruct_app2_var h2 with
          | Some ( Some "=", _,_, _), _ -> raise Exit
          | _, Some (Some "=", _,_, _) -> impl h2 (impl h1 goal l) l
          | _ -> raise Exit
          end
      | _ -> raise Exit
      with Exit -> appi (spredef_var "->" l) h1 goal l
  and ite ?(logic=true) e1 e2 e3 l = 
    let im b c = impl (eq e1 (b l) l) c l in
    if logic then and_ (im btrue_ e2) (im bfalse_ e3) l
    else
      mk (Ite (e1,e2,e3)) e2.t (NEffect.union e1.e (NEffect.union e2.e e3.e)) l
  and eq t1 t2 loc = 
    appi (pre_defvar "=" ([t1.t],[],[]) loc) t1 t2 loc
  and and_ t1 t2 loc = appi (spredef_var "/\\" loc) t1 t2 loc
  and subst x v e =
    rebuild_map
      ~varfun:(fun z i def -> if Name.equal z x then v i else def) e

  and polsubst (tvl,rvl,evl) x v e =
    let builder (tl,rl,el)= esubst evl el (rsubst rvl rl (tsubst tvl tl v)) in
    subst x builder e
  and squant k x t f loc = 
(*     Myformat.printf "squant %a: %a@." Name.print x print f; *)
    if Ty.equal t Ty.unit || Ty.equal t Ty.emptymap then f 
    else (
(*       Myformat.printf "-else-@."; *)
      try match destruct_app2_var f with
      | Some (Some "->", _, t1,f)  ->
(*           Myformat.printf "-impl-@."; *)
          begin match destruct_app2_var t1 with
          | Some (Some "=", _,({v= Var(y,_)} as t1), ({v = Var (z,_)} as t2) )->
(*               Myformat.printf "eq-sym@."; *)
              if Name.equal x y then subst x (fun _ -> t2) f
              else if Name.equal x z then subst z (fun _ -> t1) f
              else raise Exit
          | Some (Some "=", _,{v= Var(y,_)}, def)  ->
(*               Myformat.printf "eq-left@."; *)
              if Name.equal x y then subst x (fun _ -> def) f else raise Exit
          | Some (Some "=", _,def,{v = Var (y,_)}) ->
(*               Myformat.printf "eq-right@."; *)
              if Name.equal x y then subst x (fun _ -> def) f else raise Exit
          | _ -> 
(*               Myformat.printf "not eq@.";  *)
              raise Exit
          end
      | _ -> raise Exit
      with Exit -> 
        true_or f (mk (Quant (k,t,Name.close_bind x f)) f.t f.e loc) )



    
  let svar s t = var s Inst.empty (G.empty,t) 
  let le t1 t2 loc = appi (spredef_var "<=" loc) t1 t2 loc
  let pre t loc = 
    match t.t with
    | Ty.C(Ty.Tuple (t1,t2)) -> app (pre_defvar "fst" ([t1;t2],[],[]) loc) t loc
    | _ -> assert false

  let post t loc = 
    match t.t with
    | Ty.C (Ty.Tuple (t1,t2)) -> 
        app (pre_defvar "snd" ([t1;t2],[],[]) loc) t loc
    | _ -> assert false

  let encl lower i upper loc = and_ (le lower i loc) (le i upper loc) loc
  let efflam x eff e = plam x (Ty.map eff) e
  let lam x t p e q = 
    mk_val (Lam (x,t,[],p,e,q)) (Ty.arrow t e.t e.e)
  let caplam x t cap p e q = 
    mk_val (Lam (x,t,cap,p,e,q)) (Ty.caparrow t e.t e.e cap)
  let plus t1 t2 loc = appi (spredef_var "+" loc) t1 t2 loc
  let minus t1 t2 loc = appi (spredef_var "-" loc) t1 t2 loc
  let one = mk_val (Const (Const.Int Big_int.unit_big_int)) Ty.int 
  let succ t loc = plus t (one loc) loc
  let prev t loc = minus t (one loc) loc

  let param t e = mk (Param (t,e)) t e

  let mk_tuple t1 t2 loc = 
    appi (pre_defvar "," ([t1.t;t2.t],[],[]) loc) t1 t2 loc


  let letreg l e = mk (LetReg (l,e)) e.t (NEffect.rremove e.e l)

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

  let domain t = 
    match t.t with
    | Ty.C Ty.Map e -> e
    | _ -> assert false

  let combine t1 t2 l = 
    let d1 = domain t1 and d2 = domain t2 in
    if NEffect.equal d1 d2 then t2 
    else app2 (pre_defvar "combine" ([],[],[d1;d2]) l) t1 t2 l

  let set r v m l = 
    let d = domain m in
    app2 (pre_defvar "set" ([v.t],[r],[d]) l) v m l

  let restrict eff t l =
    let d = domain t in
    if NEffect.equal d eff then t else
      app (pre_defvar "restrict" ([],[],[domain t; eff]) l) t l

  let get ref map l = 
    let d = domain map in
    match ref.t with 
    | Ty.C (Ty.Ref (r,t)) ->
        app2 (pre_defvar  "!!" ([t],[r],[d]) l) ref map l
    | _ -> assert false


end

module ParseT = struct
  type t = (unit,unit,unit) t'
  type theory' = (unit,unit,unit) theory
  type theory = theory'

  let nothing _ () = ()
  let print fmt t = Print.term nothing nothing nothing (fun (_,x,e) -> x,e) fmt t
  let print_theory fmt t = 
    Print.theory nothing nothing nothing (fun (_,x,e) -> x,e) fmt t
  let mk v loc = { v = v; t = (); e = (); loc = loc }
  let pure_lam x t e = mk (PureFun (t, Name.close_bind x e))
  let annot e t = mk (Annot (e,t)) 
  let gen g e = mk (Gen (g,e)) e.loc
end
