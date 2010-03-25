(******************************************************************************)
(*                                                                            *)
(*                      Who                                                   *)
(*                                                                            *)
(*       A simple VCGen for higher-order programs.                            *)
(*                                                                            *)
(*  Copyright (C) 2009, 2010, Johannes Kanig                                  *)
(*  Contact: kanig@lri.fr                                                     *)
(*                                                                            *)
(*  Who is free software: you can redistribute it and/or modify it under the  *)
(*  terms of the GNU Lesser General Public License as published by the Free   *)
(*  Software Foundation, either version 3 of the License, or any later        *)
(*  version.                                                                  *)
(*                                                                            *)
(*  Who is distributed in the hope that it will be useful, but WITHOUT ANY    *)
(*  WARRANTY; without even the implied warranty of MERCHANTABILITY or         *)
(*  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public      *)
(*  License for more details.                                                 *)
(*                                                                            *)
(*  You should have received a copy of the GNU Lesser General Public License  *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>      *)
(******************************************************************************)

module G = Ty.Generalize
module PL = Predefined.Logic
module PI = Predefined.Identifier

type node =
  | Const of Const.t
  | Var of Name.t * inst
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t * [`Infix | `Prefix ] * Name.t list
  | Lam of Name.t * Ty.t * Name.t list * funcbody
  | Let of G.t * t * t Name.bind * isrec
  | PureFun of Ty.t * t Name.bind
  | Ite of t * t * t
  | Annot of t * Ty.t
  | Quant of [`FA | `EX ] * Ty.t * t Name.bind
  | Param of Ty.t * Effect.t
  | Gen of G.t *  t
  | HoareTriple of funcbody
  | LetReg of Name.t list * t
and t = { v : node ; t : Ty.t ; e : Effect.t; loc : Loc.loc }
and isrec = Ty.t Const.isrec
and funcbody = t * t * t
and inst = (Ty.t, Name.t, Effect.t) Inst.t

type decl =
  | Logic of Name.t * G.t * Ty.t
  | Formula of string * t * [ `Proved | `Assumed ]
  | Section of string * Const.takeover list * decl list
  | TypeDef of G.t * Ty.t option * Name.t
  | Program of Name.t * G.t * t * isrec
  | DLetReg of Name.t list
  | DGen of G.t

type theory = decl list

let map ~varfun ~varbindfun ~tyfun ~rvarfun ~effectfun f =
  let rec aux' = function
    | (Const _ ) as t -> t
    | Param (t,e) -> Param (tyfun t, effectfun e)
    | Var (v,i) -> varfun v (Inst.map tyfun rvarfun effectfun i)
    | App (t1,t2,p,cap) -> App (aux t1, aux t2, p, List.map rvarfun cap)
    | Annot (e,t) -> Annot (aux e, tyfun t)
    | Lam (x,t,cap,b) ->
        Lam (x,tyfun t, List.map rvarfun cap, body b )
    | LetReg (l,e) -> LetReg (l,aux e)
    | HoareTriple b -> HoareTriple (body b)
    | Let (g,e1,b,r) -> Let (g,aux e1,varbindfun b, r)
    | PureFun (t,b) -> PureFun (tyfun t, varbindfun b)
    | Ite (e1,e2,e3) -> Ite (aux e1, aux e2, aux e3)
    | Quant (k,t,b) -> Quant (k,tyfun t,varbindfun b)
    | Gen (g,e) -> Gen (g,aux e)
  and body (p,e,q) = aux p, aux e, aux q
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
  | LetReg _, _ | Annot _, _ | Param _, _
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
    | Quant _ | Param _ | LetReg _ | Gen _ | HoareTriple _ -> true
  let is_compound_node t = is_compound t.v

  type sup = [ `Coq | `Who | `Pangoline ]
  let name_print ?(kind : sup =`Who) fmt x =
    match kind with
    | `Pangoline ->
        begin try
          let s = PL.get_pangoline_id x in
          pp_print_string fmt s
        with Not_found -> Name.print fmt x end
    | `Coq | `Who -> Name.print fmt x

  let maycaplist fmt l =
    if l = [] then ()
    else fprintf fmt "allocates %a" (print_list space Name.print) l

  let prrec fmt = function
    | Const.NoRec -> ()
    | Const.Rec t -> fprintf fmt "rec(%a) " Ty.print t
    | Const.LogicDef -> fprintf fmt "logic "

  let lname s fmt l =
    if l = [] then () else
    fprintf fmt "(%a :@ %s)" (print_list space Name.print) l s

  let inst ~kind = 
    Inst.print ~kind ~intype:false 
      (Ty.gen_print ~kind) Name.print Effect.print

  (* TODO factorize the different branches *)
  let term ?(kind : sup =`Who) open_ fmt t =
    let typrint = Ty.gen_print ~kind in
    let rec print' fmt = function
      | Const c -> Const.print fmt c
      | App ({v = App ({ v = Var(v,i)},t1,_,_)},t2,`Infix,_) ->
          fprintf fmt "@[%a@ %a%a@ %a@]" with_paren t1 (name_print ~kind) v
            (inst ~kind) i with_paren t2
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
          fprintf fmt "@[let@ %a%a %a=@[@ %a@]@ in@ %a@]"
            prrec r Name.print x G.print g print e1 print e2
      | Var (v,i) ->
          begin match kind with
          | `Who | `Pangoline ->
              let pr fmt () =
                if Inst.is_empty i then (name_print ~kind) fmt v
                else fprintf fmt "%a %a" (name_print ~kind) v (inst ~kind) i
              in
              pr fmt ()
          | `Coq -> Name.print fmt v
          end
      | Annot (e,t) -> fprintf fmt "(%a : %a)" print e typrint t
      | Quant (k,t,b) ->
          let x,e = open_ b in
          let bind = if k = `FA then binder else binder' false in
          fprintf fmt "@[%a %a%a@ %a@]" Const.quant k bind (x,t)
            Const.quantsep kind print e
      | Gen ((tl,_,_) as g,t) ->
          if G.is_empty g then print fmt t else
            begin match kind with
            | `Coq ->
                fprintf fmt "forall@ %a,@ %a " (lname "Type") tl print t
            | `Pangoline  ->
                fprintf fmt "forall type %a. %a"
                  (print_list space Name.print) tl print t
            | `Who ->
                fprintf fmt "forall %a%a %a"
                  G.print g Const.quantsep kind print t
            end
      (* specific to Who, will not be printed in backends *)
      | Param (t,e) ->
          fprintf fmt "parameter(%a,%a)"
            typrint t Effect.print e
      | HoareTriple (p,f,q) ->
          fprintf fmt "[[%a]]%a[[%a]]" print p print f print q
      | LetReg (v,t) ->
          fprintf fmt "@[letregion %a in@ %a@]"
            (print_list space Name.print) v print t
      | Lam (x,t,cap,(p,e,q)) ->
          fprintf fmt "@[(fun %a@ ->%a@ {%a}@ %a@ {%a})@]"
            binder (x,t) maycaplist cap print p print e print q

    and print fmt t = print' fmt t.v
    and binder' par =
      let p fmt (x,t) = fprintf fmt "%a:%a"
        Name.print x typrint t in
      if par then paren p else p
    and binder fmt b = binder' true fmt b
    and maycap fmt = function
      | [] -> ()
      | l -> fprintf fmt "{%a}" (print_list space Name.print) l
    and with_paren fmt x =
      if is_compound_node x then paren print fmt x else print fmt x in
    print fmt t

  let decl ?(kind=`Who) open_ fmt d =
    let typrint = Ty.gen_print ~kind in
    let term = term ~kind open_ in
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
          | None -> fprintf fmt "@[type %a%a@]" Name.print x G.print g
          | Some t ->
              fprintf fmt "@[<hov 2>type %a%a =@ %a@]"
                Name.print x G.print g typrint t
          end
      | DLetReg l ->
          fprintf fmt "@[letregion %a@]" (print_list space Name.print) l
      | Section (s,cl,d) ->
          fprintf fmt "@[<hov 2>section %s@, %a@, %a@] end" s
          (print_list newline Const.takeover) cl decl_list d
      | Program (x,g,t,r) ->
          fprintf fmt "@[<hov 2>let@ %a%a %a = %a @]" prrec r
          Name.print x G.print g term t
      | DGen g ->
          fprintf fmt "@[INTROS %a@]" G.print g
    and decl_list fmt d = print_list newline decl fmt d in
    decl fmt d

  let theory ?kind open_ fmt t =
    print_list newline (decl ?kind open_) fmt t
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
  Print.term ~kind sopen fmt t
let coq_print fmt t = gen_print `Coq fmt t
let print fmt t = gen_print `Who fmt t

let print_decl = Print.decl ~kind:`Who sopen
let print_theory = Print.theory ~kind:`Who sopen

let print' fmt t =
  print fmt {v = t; t = Ty.unit; e = Effect.empty; loc = Loc.dummy }

let mk v t e loc = { v = v; t = t; e = e; loc = loc }
let mk_val v t loc = { v = v; t = t; e = Effect.empty; loc = loc }

let ptrue_ loc = mk_val (Const Const.Ptrue) Ty.prop loc
let pfalse_ loc = mk_val (Const Const.Pfalse) Ty.prop loc

let const c =
  mk_val (Const c) (Ty.const (Const.type_of_constant c))

let simple_var v t = mk_val (Var (v, Inst.empty)) t
let simple_var_id s =
  let x, (_,t) = PL.var_and_type s in
  simple_var x t

let mempty l = simple_var_id PI.empty_id l
let btrue_ l = simple_var_id PI.btrue_id l
let bfalse_ l = simple_var_id PI.bfalse_id l
let void l = simple_var_id PI.void_id l

let var s inst (g,t) =
  let nt = (Ty.allsubst g inst t) in
  if Ty.equal nt Ty.unit then void
  else if Ty.equal nt Ty.emptymap then mempty
  else mk_val (Var (s,inst)) nt

let var_i s inst t = mk_val (Var (s,inst)) t
let svar s t = var s Inst.empty (G.empty, t)

let predef s i = 
  let x, t = PL.var_and_type s in
  var x i t 

let spredef s = 
  let x, (_,t) = PL.var_and_type s in
  svar x t 

let true_or e v =
  match e.v with
  | Const Const.Ptrue -> e
  | _ -> v

let annot e t = true_or e (mk (Annot (e,t)) t e.e e.loc)

let domain t =
  match t.t with
  | Ty.Map e -> e
  | _ -> assert false

let let_ g e1 x e2 r l =
  true_or e2
    (mk (Let (g, e1,Name.close_bind x e2,r)) e2.t
      (Effect.union e1.e e2.e) l)

let plam x t e loc =
  mk_val (PureFun (t,Name.close_bind x e)) (Ty.parr t e.t) loc

let hoare_triple p e q l = mk_val (HoareTriple (p,e,q)) Ty.prop l

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
  let eq = Predefined.Logic.equal in
  match x with
  | x when eq x PI.leb_id -> fun _ -> spredef PI.le_id
  | x when eq x PI.ltb_id -> fun _ -> spredef PI.lt_id
  | x when eq x PI.geb_id -> fun _ -> spredef PI.ge_id
  | x when eq x PI.gtb_id -> fun _ -> spredef PI.gt_id
  | x when eq x PI.eqb_id -> predef PI.equal_id
  | x when eq x PI.neqb_id -> predef PI.neq_id
  | x when eq x PI.andb_id -> fun _ -> spredef PI.and_id
  | x when eq x PI.orb_id -> fun _ -> spredef PI.or_id
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
        | Some (v,_) when PL.equal v PI.and_id -> and_ t1 t2 l
        | Some (v,_) when PL.equal v PI.impl_id -> impl t1 t2 l
        | Some (v,_) when PL.equal v PI.equal_id -> eq t1 t2 l
        | Some (v,_) when PL.equal v PI.combine_id -> combine t1 t2 l
        | _ -> raise Exit
        end
    | _ ->
    (* simple application *)
        match destruct_varname t1 with
        | Some (v,_) when PL.equal v PI.not_id -> neg t2 l
        | Some (v, _) when PL.equal v PI.fst_id -> pre t2 l
        | Some (v, _) when PL.equal v PI.snd_id -> post t2 l
        | Some (v, ([],[],[_;b])) when PL.equal v PI.restrict_id ->
            restrict b t2 l
        | _ -> raise Exit
    with Exit -> simple_app ?kind ?cap t1 t2 l

and app2 ?kind t t1 t2 loc = app ?kind (app t t1 loc) t2 loc
and appi t t1 t2 loc = app2 ~kind:`Infix t t1 t2 loc
and allapp t1 t2 kind cap loc = app ~kind ~cap t1 t2 loc
and appn t tl loc =
  List.fold_left (fun acc t -> app acc t loc) t tl

and neg f l =
  match f.v with
  | Const Const.Ptrue -> pfalse_ l
  | Const Const.Pfalse -> ptrue_ l
  | _ -> simple_app (spredef PI.not_id l) f l

and reduce_bool t l =
  let rec aux t =
    match t.v with
    | Var (v,_) when PL.equal v PI.btrue_id -> ptrue_ l
    | _ ->
        match destruct_app2_var t with
        | Some (op, i, arg1, arg2) ->
            let v = boolcmp_to_propcmp op in
            let arg1, arg2 =
              if PL.equal op PI.andb_id || PL.equal op PI.orb_id then
                aux arg1, aux arg2
              else arg1, arg2 in
            appi (v i l) arg1 arg2 l
        | None -> raise Exit in
  aux t
and rebuild_map ~varfun ~termfun ?(tyfun = (fun x -> x)) t =
  (* this function is intended to be used with logic functions only *)
  let l = t.loc in
  let rec aux t =
    let t =
      match t.v with
      | Const _ -> t
      | Var (v,i) -> varfun v (Inst.map tyfun Misc.id Misc.id i) t
      | App (t1,t2,p,cap) -> allapp (aux t1) (aux t2) p cap l
      | Annot (e,t) -> annot (aux e) (tyfun t)
      | Let (g,e1,b,r) ->
          let x,f = vopen b in
          let_ g (aux e1) x (aux f) r l
      | PureFun (t,b) ->
          let x,f = vopen b in
          plam x (tyfun t) (aux f) l
      | Quant (k,t,b) ->
          let x,f = vopen b in
          squant k x (tyfun t) (aux f) l
      | Ite (e1,e2,e3) -> ite ~logic:false (aux e1) (aux e2) (aux e3) l
      | Gen (g,e) -> gen g (aux e) l
      | HoareTriple (p,e,q) ->
          hoare_triple (aux p) (aux e) (aux q) l
      | LetReg _ | Param _ | Lam _ -> assert false in
    termfun t
  in
  aux t
and impl h1 goal l =
(*     Myformat.printf "impl: %a and %a@." print h1 print goal; *)
  try match destruct_app2_var h1 with
  | Some (v, _, ha, hb) when PL.equal v PI.and_id ->
      impl ha (impl hb goal l) l
  | _ ->
      match destruct_app2_var goal with
      | Some (v, _, h2, goal) when PL.equal v PI.and_id ->
          begin match destruct_app2_var h1,destruct_app2_var h2 with
          | Some ( v, _,_, _), _ when PL.equal v PI.equal_id -> raise Exit
          | _, Some (v, _,_, _) when PL.equal v PI.equal_id ->
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
  with Exit -> simple_appi (spredef PI.impl_id l) h1 goal l
and ite ?(logic=true) e1 e2 e3 l =
  let im b c = impl (eq e1 (b l) l) c l in
  if logic then and_ (im btrue_ e2) (im bfalse_ e3) l
  else
    mk (Ite (e1,e2,e3)) e2.t (Effect.union e1.e (Effect.union e2.e e3.e)) l
and eq t1 t2 l =
  if equal t1 t2 then ptrue_ l
  else
    try match t2.v with
    | Var (v, ([], [], [])) when
       PL.equal v PI.btrue_id || PL.equal v PI.bfalse_id ->
        let f = reduce_bool t1 l in
        if PL.equal v PI.btrue_id then f else neg f l
    | _ -> raise Exit
    with Exit -> simple_appi (predef PI.equal_id ([t1.t],[],[]) l) t1 t2 l
and and_ t1 t2 l =
  match t1.v,t2.v with
  | Const Const.Ptrue, _ -> t2
  | _, Const Const.Ptrue -> t1
  | Const Const.Pfalse, _ -> t1
  | _, Const Const.Pfalse -> t2
  | _ -> simple_appi (spredef PI.and_id l) t1 t2 l
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
    | Some (i, _, t1,f) when PL.equal i PI.impl_id ->
        begin match destruct_app2_var t1 with
        | Some (e, _,({v= Var(y,_)} as t1), ({v = Var (z,_)} as t2) )
          when PL.equal e PI.equal_id ->
            if Name.equal x y then subst x (fun _ -> t2) f
            else if Name.equal x z then subst z (fun _ -> t1) f
            else raise Exit
        | Some (e, _,{v= Var(y,_)}, def)
            when PL.equal e PI.equal_id ->
            if Name.equal x y then subst x (fun _ -> def) f else raise Exit
        | Some (e, _,def,{v = Var (y,_)})
            when PL.equal e PI.equal_id ->
            if Name.equal x y then subst x (fun _ -> def) f else raise Exit
        | _ ->
            raise Exit
        end
    | _ -> raise Exit
    with Exit ->
      true_or f (mk (Quant (k,t,Name.close_bind x f)) f.t f.e loc) )

and pre t l =
  match destruct_app2_var t with
  | Some (v,_,a,_) when PL.equal v (PI.mk_tuple_id 2) -> a
  | _ ->
      try
        let t1, t2 = Ty.destr_pair t.t in
        simple_app (predef PI.fst_id ([t1;t2],[],[]) l) t l
      with Invalid_argument "Ty.destr_tuple" ->
        error t.loc "term %a is not of tuple type, but of type %a@."
          print t Ty.print t.t


and post t l =
  match destruct_app2_var t with
  | Some (v,_,_,b) when PL.equal v (PI.mk_tuple_id 2) -> b
  | _ ->
      try
        let t1, t2 = Ty.destr_pair t.t in
        simple_app (predef PI.snd_id ([t1;t2],[],[]) l) t l
      with Invalid_argument "Ty.destr_tuple" ->
        error t.loc "term %a is not of tuple type, but of type %a@."
          print t Ty.print t.t
and combine t1 t2 l =
  let d1 = domain t1 and d2 = domain t2 in
  if Effect.is_empty d2 then t1
  else
    let d1', d2', d3' = Effect.split d1 d2 in
    if Effect.is_empty d1' then t2
    else
      match destruct_app2_var t1 with
      | Some (v,([],[],[e1;_;_]), _, db)
        when PL.equal v PI.combine_id && Effect.sub_effect e1 d2' ->
          combine db t2 l
      | _  -> 
          simple_app2 (predef PI.combine_id ([],[],[d1';d2';d3']) l) t1 t2 l

and restrict eff t l =
  let d = Effect.diff (domain t) eff in
  if Effect.is_empty d then t else
  try
    match destruct_app2_var t with
    | Some (v,([],[],[e1;_;e3]), m1, m2)
      when PL.equal v PI.combine_id  ->
        if Effect.sub_effect eff e3 then restrict eff m2 l
        else if Effect.sub_effect eff e1 then restrict eff m1 l
        else raise Exit
    | _ -> raise Exit
  with Exit -> simple_app (predef PI.restrict_id ([],[],[d; eff]) l) t l


let svar s t = var s Inst.empty (G.empty,t)
let le t1 t2 loc = simple_appi (spredef PI.le_id loc) t1 t2 loc

let encl lower i upper loc = and_ (le lower i loc) (le i upper loc) loc
let efflam x eff e = plam x (Ty.map eff) e
let lam x t p e q =
  mk_val (Lam (x,t,[],(p,e,q))) (Ty.arrow t e.t e.e)
let caplam x t cap p e q =
  mk_val (Lam (x,t,cap,(p,e,q))) (Ty.caparrow t e.t e.e cap)
let plus t1 t2 loc = appi (spredef PI.plus_id loc) t1 t2 loc
let minus t1 t2 loc = appi (spredef PI.minus_id loc) t1 t2 loc
let one = mk_val (Const (Const.Int Big_int.unit_big_int)) Ty.int
let succ t loc = plus t (one loc) loc
let prev t loc = minus t (one loc) loc

let param t e = mk (Param (t,e)) t e

let mk_tuple t1 t2 loc =
  appi (predef (PI.mk_tuple_id 2) ([t1.t;t2.t],[],[]) loc) t1 t2 loc


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

let rec is_value x =
  match x.v with
  | Const _ | Var _ | Lam _ | PureFun _ | Quant _ | HoareTriple _ -> true
  | Let _ | Ite _ | LetReg _ | Param _ -> false
  | Annot (e,_) | Gen (_,e) -> is_value e
  | App (t1,_,_,_) ->
      match t1.t with
      | Ty.PureArr _ -> true
      | _ -> false

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
  | Lam (_,_,_,(_,e,_)) -> is_param e
  | PureFun (_,(_,_,e)) -> is_param e
  | _ -> false

let destruct_restrict' x =
  match destruct_app' x with
  | Some ({v = Var (v,([],[],[e1;e2]))},map)
    when PL.equal v PI.restrict_id ->
      Some (map,e1,e2)
  | _ -> None

let destruct_get' x =
  match destruct_app2_var' x with
  | Some (v, ([t],[reg],[e]), r,map) when PL.equal v PI.get_id ->
      Some (t,r,reg,Effect.radd e reg,map)
  | _ -> None

let destruct_get x = destruct_get' x.v

let get ref map l =
  match ref.t with
  | Ty.Ref (r,t) ->
      let d = domain map in
      let d = Effect.rremove d [r] in
      simple_app2 (predef PI.get_id ([t],[r],[d]) l) ref map l
  | _ -> assert false

let rec decl_map ~varfun ~termfun ~declfun d : decl list =
  let d =
    match d with
    | Logic _ | TypeDef _ | DLetReg _ | DGen _ -> d
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
