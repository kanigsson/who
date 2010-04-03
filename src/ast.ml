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
module PL = Predefined
module I = Identifiers

type var = { var : Name.t; scheme : Ty.scheme }

type node =
  | Const of Const.t
  | Var of var * inst
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t * [`Infix | `Prefix ] * Name.t list
  | Lam of Name.t * Ty.t * Name.t list * funcbody
  | Let of G.t * t * t Name.bind * isrec
  | PureFun of Ty.t * t Name.bind
  | Ite of t * t * t
  | Quant of [`FA | `EX ] * Ty.t * t Name.bind
  | Param of Ty.t * Rw.t
  | Gen of G.t *  t
  | HoareTriple of funcbody
  | LetReg of Name.t list * t
and t = { v : node ; t : Ty.t ; e : Rw.t; loc : Loc.loc }
and isrec = Ty.t Const.isrec
and funcbody = t * t * t
and inst = (Ty.t, Name.t, Effect.t) Inst.t

type decl =
  | Logic of Name.t * Ty.scheme
  | Formula of Name.t * t * [ `Proved | `Assumed ]
  | Section of Name.t *  decl list * section_kind
  | TypeDef of Name.t list * Name.t
  | Program of Name.t * G.t * t * isrec
  | Inductive of Name.t * G.t * Ty.t * t list
  | DLetReg of Name.t list
  | DGen of G.t
  | Decl of string
and section_kind =
    [ `Block of Const.takeover list | `Structure ]

type theory = decl list

let map ~varfun ~varbindfun ~tyfun ~rvarfun ~effectfun f =
  let rec aux' = function
    | (Const _ ) as t -> t
    | Param (t,e) -> Param (tyfun t, rwfun e)
    | Var (v,i) -> Var (var v, Inst.map tyfun rvarfun effectfun i)
    | App (t1,t2,p,cap) -> App (aux t1, aux t2, p, List.map rvarfun cap)
    | Lam (x,t,cap,b) ->
        Lam (x,tyfun t, List.map rvarfun cap, body b )
    | LetReg (l,e) -> LetReg (l,aux e)
    | HoareTriple b -> HoareTriple (body b)
    | Let (g,e1,b,r) -> Let (g,aux e1,varbindfun b, r)
    | PureFun (t,b) -> PureFun (tyfun t, varbindfun b)
    | Ite (e1,e2,e3) -> Ite (aux e1, aux e2, aux e3)
    | Quant (k,t,b) -> Quant (k,tyfun t,varbindfun b)
    | Gen (g,e) -> Gen (g,aux e)
  and rwfun e = Rw.map effectfun e
  and body (p,e,q) = aux p, aux e, aux q
  and var v = 
    let (g,t) = v.scheme in
    { var = varfun v.var ; scheme = g, tyfun t }
  and aux t = {t with v = aux' t.v; t = tyfun t.t; e = rwfun t.e} in
  aux f

let refresh s t =
  map ~varfun:(Name.refresh s)
    ~varbindfun:(Name.refresh_bind s)
    ~tyfun:Misc.id
    ~rvarfun:Misc.id
    ~effectfun:Misc.id t

let vopen = Name.open_bind refresh
let close = Name.close_bind
let sopen = Name.sopen refresh
let vopen_with x = Name.open_with refresh x

let var_equal v1 v2 =
  Name.equal v1.var v2.var && Ty.scheme_equal v1.scheme v2.scheme

let rec equal' a b =
  match a, b with
  | Const c1, Const c2 -> Const.compare c1 c2 = 0
  | Var (v1,i1), Var (v2,i2) ->
      var_equal v1 v2 &&
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
  | LetReg _, _ | Param _, _
  | Lam _, _ -> assert false
  | _, _ -> false
and bind_equal b1 b2 =
  (let x,eb1 = vopen b1 in
   let eb2 = vopen_with x b2 in
   equal eb1 eb2)

and equal a b = equal' a.v b.v

module Convert = struct

  module P = PrintTree

  let id = Name.Env.id
  let gen = Ty.Convert.gen
  let ty = Ty.Convert.t
  let scheme = Ty.Convert.scheme
  let effect = Effect.Convert.t
  let rw = Rw.Convert.t

  let inst env i = Inst.map (ty env) (id env) (effect env) i
  let rrec env r =
    match r with
    | Const.LogicDef -> Const.LogicDef
    | Const.NoRec -> Const.NoRec
    | Const.Rec t -> Const.Rec (ty env t)

  let rec t env term =
    match term.v with
    | Const c -> P.Const c
    | Param (t,e) -> P.Param (ty env t, rw env e)
    | Var (v,i) ->
        let s = id env v.var in
        P.Var (s, inst env i)
    | App (t1,t2,p,cap) ->
        P.App (t env t1, t env t2, p, List.map (id env) cap)
    | LetReg (l,e) ->
        let env = Name.Env.add_id_list env l in
        P.LetReg (List.map (id env) l,t env e)
    | Lam (x,at,cap,b) ->
        let env = Name.Env.add_id env x in
        P.Lam (id env x,ty env at, List.map (id env) cap, body env b )
    | HoareTriple b -> P.HoareTriple (body env b)
    | PureFun (at,b) ->
        let x,e = vopen b in
        let env = Name.Env.add_id env x in
        P.PureFun (id env x, ty env at, t env e )
    | Quant (k,at,b) ->
        let x,e = vopen b in
        let env = Name.Env.add_id env x in
        P.Quant (k,id env x, ty env at,t env e)
    | Let (g,e1,b,r) ->
        let x, e2 = vopen b in
        let env', g = gen env g in
        let e1 = t env' e1 in
        let env = Name.Env.add_id env x in
        P.Let (g,e1,id env x, t env e2, rrec env r)
    | Ite (e1,e2,e3) -> P.Ite (t env e1, t env e2, t env e3)
    | Gen (g,e) ->
        let env, g = gen env g in
        P.Gen (g,t env e)
  and body env (t1,t2,t3) = t env t1, t env t2, t env t3

  let add_id = Name.Env.add_id
  let add_ids = Name.Env.add_id_list

  let rec decl env d =
    match d with
    | Logic (n,s) ->
        let env = add_id env n in
        env, P.Logic (id env n, scheme env s)
    | Formula (s,f,k) ->
        let env = add_id env s in
        env, P.Formula (id env s,t env f, k)
    | DLetReg nl ->
        let env = add_ids env nl in
        env, P.DLetReg (List.map (id env) nl)
    | DGen g ->
        let env, g = gen env g in
        env, P.DGen g
    | Program (n,g,e,r) ->
        let env',g = gen env g in
        let e = t env' e in
        let r = rrec env r in
        let env = add_id env n in
        env, P.Program (id env n,g,e,r)
    | TypeDef (tl,n) ->
        let env = add_id env n in
        let env' = add_ids env tl in
        env, P.TypeDef (List.map (id env') tl,id env n)
    | Section (s,dl, kind) ->
        let env = add_id env s in
        let env, th = theory env dl in
        env, P.Section (id env s,th, kind)
    | Decl s -> env, P.Decl s
    | Inductive (n,g,ity,tl) ->
        let env = add_id env n in
        let env', g = gen env g in
        let args,_ = Ty.nsplit ity in
        env, P.Inductive (id env n, g,
          List.map (ty env') args, List.map (t env') tl)
  and theory env th =
    ExtList.fold_map decl env th


end
module Print = struct

  let predef kind =
    match kind with
    | `Who -> Name.M.empty
    | `Coq -> Predefined.coq_map ()
    | `Pangoline -> Predefined.pangoline_map ()

  let empty ?(kind=`Who) () = Name.Env.empty (predef kind)

  let term ?kind fmt t =
    PrintTree.Print.term ?kind fmt (Convert.t (empty ?kind ()) t)

  let decl ?kind fmt d =
    let _, d = Convert.decl (empty ?kind ()) d in
    PrintTree.Print.decl false ?kind fmt d

  let theory ?kind fmt th =
    let _, th = Convert.theory (empty ?kind ()) th in
    PrintTree.Print.theory ?kind fmt th

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

let is_equality t =
  match destruct_app2_var t with
  | Some (v, _, _,_) when PL.equal v.var I.equal_id -> true
  | _ -> false

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
  open_close_map ~varfun:Misc.id
                 ~tyfun:(Ty.tlsubst tvl tl)
                 ~rvarfun:Misc.id
                 ~effectfun:Misc.id
                 e

let rsubst rvl rl e =
  open_close_map ~varfun:Misc.id
                 ~tyfun:(Ty.rlsubst rvl rl)
                 ~rvarfun:(Ty.rsubst rvl rl)
                 ~effectfun:(Effect.rmap (Ty.rsubst rvl rl))
                 e

let esubst evl el e =
  open_close_map ~varfun:Misc.id
    ~tyfun:(Ty.elsubst evl el)
    ~rvarfun:Misc.id
    ~effectfun:(Effect.lsubst evl el) e

let allsubst ((tvl,rvl,evl) : G.t) ((tl,rl,el) : inst)  t =
  esubst evl el (rsubst rvl rl (tsubst tvl tl t))

let gen_print kind fmt t = Print.term ~kind fmt t
let coq_print fmt t = gen_print `Coq fmt t
let print fmt t = gen_print `Who fmt t

let print_decl = Print.decl ~kind:`Who
let print_theory = Print.theory ~kind:`Who

let print' fmt t =
  print fmt {v = t; t = Ty.prop; e = Rw.empty; loc = Loc.dummy }

let mk v t e loc = { v = v; t = t; e = e; loc = loc }
let mk_val v t loc = { v = v; t = t; e = Rw.empty; loc = loc }

let ptrue_ loc = mk_val (Const Const.Ptrue) Ty.prop loc
let pfalse_ loc = mk_val (Const Const.Pfalse) Ty.prop loc

let const c =
  mk_val (Const c) (Ty.const (Const.type_of_constant c))

let simple_var v t = mk_val (Var (v, Inst.empty)) t
let mk_var_with_scheme v s = { var = v; scheme = s }
let mk_var_with_type v t = { var = v; scheme = Ty.as_scheme t }
let simple_var_id s =
  let x, ((_,t) as s) = PL.var_and_type s in
  simple_var (mk_var_with_scheme x s) t

let mempty l = simple_var_id I.empty_id l
let btrue_ l = simple_var_id I.btrue_id l
let bfalse_ l = simple_var_id I.bfalse_id l
let void l = simple_var_id I.void_id l

let var x inst =
  try
    let g,t = x.scheme in
    let nt = (Ty.allsubst g inst t) in
    if Ty.is_unit nt then void
    else if Ty.equal nt Ty.emptymap then mempty
    else mk_val (Var (x,inst)) nt
  with Invalid_argument _ ->
    failwith (Myformat.sprintf "%a : not the right number of effect
    instantiations" Name.print x.var)

let svar s = var s Inst.empty

let predef s i =
  let x, t = PL.var_and_type s in
  let v = mk_var_with_scheme x t in
  var v i

let spredef s =
  predef s Inst.empty

let true_or e v =
  match e.v with
  | Const Const.Ptrue -> e
  | _ -> v

let domain t =
  match t.t with
  | Ty.Map e -> e
  | _ -> assert false

let let_ g e1 x e2 r l =
  true_or e2
    (mk (Let (g, e1,Name.close_bind x e2,r)) e2.t
      (Rw.union e1.e e2.e) l)

let plam x t e loc =
  mk_val (PureFun (t,Name.close_bind x e)) (Ty.parr t e.t) loc

let hoare_triple p e q l = mk_val (HoareTriple (p,e,q)) Ty.prop l

let gen g e l = true_or e (mk (Gen (g, e)) e.t e.e l)

let simple_app ?(kind=`Prefix) ?(cap=[]) t1 t2 l =
  try
    let t = Ty.result t1.t and e = Ty.latent_effect t1.t in
    if not (Ty.equal (Ty.arg t1.t) t2.t) then raise Exit;
    mk (App (t1,t2,kind,cap)) t (Rw.union3 t1.e t2.e e) l
  with
  | Exit ->
      Myformat.printf "type mismatch on application: function %a has type %a,
        and argument %a has type %a@." print t1 Ty.print t1.t
        print t2 Ty.print t2.t ;
      invalid_arg "app"
  | Invalid_argument _ ->
      Myformat.printf "not a function: %a of type %a.." print t1 Ty.print t1.t;
      invalid_arg "app"


let simple_app2 ?kind t t1 t2 loc =
  simple_app ?kind (simple_app t t1 loc) t2 loc
let simple_appi t t1 t2 loc = simple_app2 ~kind:`Infix t t1 t2 loc

let simple_eq t1 t2 l =
  simple_appi (predef I.equal_id ([t1.t],[],[]) l) t1 t2 l

let id_equal v id = PL.equal v.var id

let boolcmp_to_propcmp x =
  let eq = Predefined.equal in
  match x with
  | x when eq x I.leb_id -> fun _ -> spredef I.le_id
  | x when eq x I.ltb_id -> fun _ -> spredef I.lt_id
  | x when eq x I.geb_id -> fun _ -> spredef I.ge_id
  | x when eq x I.gtb_id -> fun _ -> spredef I.gt_id
  | x when eq x I.eqb_id -> predef I.equal_id
  | x when eq x I.neqb_id -> predef I.neq_id
  | x when eq x I.andb_id -> fun _ -> spredef I.and_id
  | x when eq x I.orb_id -> fun _ -> spredef I.or_id
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
        | Some (v,_) when id_equal v I.and_id -> and_ t1 t2 l
        | Some (v,_) when id_equal v I.or_id -> or_ t1 t2 l
        | Some (v,_) when id_equal v I.impl_id -> impl t1 t2 l
        | Some (v,_) when id_equal v I.equal_id -> eq t1 t2 l
        | Some (v,_) when id_equal v I.combine_id -> combine t1 t2 l
        | _ -> raise Exit
        end
    | _ ->
    (* simple application *)
        match destruct_varname t1 with
        | Some (v,_) when id_equal v I.not_id -> neg t2 l
        | Some (v, _) when id_equal v I.fst_id -> pre t2 l
        | Some (v, _) when id_equal v I.snd_id -> post t2 l
        | Some (v, ([],[],[_;b])) when id_equal v I.restrict_id ->
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
  | _ -> simple_app (spredef I.not_id l) f l

and reduce_bool t l =
  let rec aux t =
    match t.v with
    | Var (v,_) when id_equal v I.btrue_id -> ptrue_ l
    | _ ->
        match destruct_app2_var t with
        | Some (op, i, arg1, arg2) ->
            let v = boolcmp_to_propcmp op.var in
            let arg1, arg2 =
              if id_equal op I.andb_id || id_equal op I.orb_id then
                aux arg1, aux arg2
              else arg1, arg2 in
            appi (v i l) arg1 arg2 l
        | None -> raise Exit in
  aux t
and rebuild_map ?(varfun = Misc.k3) ?(termfun = Misc.id) ?(tyfun = Misc.id) =
  (* this function is intended to be used with logic functions only *)
  if varfun == Misc.k3 && termfun == Misc.id && tyfun == Misc.id then
    (fun t -> t)
  else
    fun t ->
  let l = t.loc in
  let rec aux t =
    let t =
      match t.v with
      | Const _ -> t
      | Var (v,i) -> varfun v.var (Inst.map tyfun Misc.id Misc.id i) t
      | App (t1,t2,p,cap) -> allapp (aux t1) (aux t2) p cap l
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
  | Some (v, _, ha, hb) when id_equal v I.and_id ->
      impl ha (impl hb goal l) l
  | _ ->
      match destruct_app2_var goal with
      | Some (v, _, h2, goal) when id_equal v I.impl_id ->
          if is_equality h1 then raise Exit
          else if is_equality h2 then impl h2 (impl h1 goal l) l
          else raise Exit
      | _ -> raise Exit
  with Exit ->
    match h1.v,goal.v with
    | Const Const.Ptrue, _ -> goal
    | _, Const Const.Ptrue -> goal
    | Const Const.Pfalse, _ -> ptrue_ l
    | _, _ when equal h1 goal -> ptrue_ l
    | _ -> simple_appi (spredef I.impl_id l) h1 goal l

and ite ?(logic=true) e1 e2 e3 l =
  let im b c = impl (eq e1 (b l) l) c l in
  if logic then and_ (im btrue_ e2) (im bfalse_ e3) l
  else
    mk (Ite (e1,e2,e3)) e2.t (Rw.union3 e1.e e2.e e3.e) l
and eq t1 t2 l =
  if equal t1 t2 then ptrue_ l
  else
    try match t2.v with
    | Var (v, ([], [], [])) when
       id_equal v I.btrue_id || id_equal v I.bfalse_id ->
        let f = reduce_bool t1 l in
        if id_equal v I.btrue_id then f else neg f l
    | _ -> raise Exit
    with Exit ->
      match t1.v, t2.v with
      | Var (v1,([],[],[])), Var (v2, ([],[],[])) ->
          if Name.compare v2.var v1.var < 0 then simple_eq t2 t1 l
          else simple_eq t1 t2 l
      | Var _, _ -> simple_eq t1 t2 l
      | _, Var _ -> simple_eq t2 t1 l
      | _, _ -> simple_eq t1 t2 l

and and_ t1 t2 l =
  match t1.v,t2.v with
  | Const Const.Ptrue, _ -> t2
  | _, Const Const.Ptrue -> t1
  | Const Const.Pfalse, _ -> t1
  | _, Const Const.Pfalse -> t2
  | _ -> simple_appi (spredef I.and_id l) t1 t2 l

and or_ t1 t2 l =
  match t1.v,t2.v with
  | Const Const.Ptrue, _ -> t1
  | _, Const Const.Ptrue -> t2
  | Const Const.Pfalse, _ -> t2
  | _, Const Const.Pfalse -> t1
  | _ -> simple_appi (spredef I.or_id l) t1 t2 l
and subst x v e =
(*     Myformat.printf "subst: %a@." Name.print x ; *)
  rebuild_map
    ~varfun:(fun z i def -> if Name.equal z x then v i else def)
    ~termfun:Misc.id e

and polsubst g x v e = subst x (fun i -> allsubst g i v) e
and squant k x t f loc =
  if Ty.is_unit t || Ty.equal t Ty.emptymap then f
  else
  begin
    try match destruct_app2_var f with
    | Some (i, _, t1,f) when id_equal i I.impl_id ->
        begin match destruct_app2_var t1 with
        | Some (e, _,({v= Var(y,_)} as t1), ({v = Var (z,_)} as t2) )
          when id_equal e I.equal_id ->
            if Name.equal x y.var then subst x (fun _ -> t2) f
            else if Name.equal x z.var then subst z.var (fun _ -> t1) f
            else raise Exit
        | Some (e, _,{v= Var(y,_)}, def) when id_equal e I.equal_id ->
            if Name.equal x y.var then subst x (fun _ -> def) f
            else raise Exit
        | Some (e, _,def,{v = Var (y,_)}) when id_equal e I.equal_id ->
            if Name.equal x y.var then subst x (fun _ -> def) f
            else raise Exit
        | _ -> raise Exit
        end
    | _ -> raise Exit
    with Exit ->
      true_or f (mk (Quant (k,t,Name.close_bind x f)) f.t f.e loc)
  end

and pre t l =
  match destruct_app2_var t with
  | Some (v,_,a,_) when id_equal v (I.mk_tuple_id 2) -> a
  | _ ->
      try
        let t1, t2 = Ty.destr_pair t.t in
        simple_app (predef I.fst_id ([t1;t2],[],[]) l) t l
      with Invalid_argument "Ty.destr_tuple" ->
        error t.loc "term %a is not of tuple type, but of type %a@."
          print t Ty.print t.t


and post t l =
  match destruct_app2_var t with
  | Some (v,_,_,b) when id_equal v (I.mk_tuple_id 2) -> b
  | _ ->
      try
        let t1, t2 = Ty.destr_pair t.t in
        simple_app (predef I.snd_id ([t1;t2],[],[]) l) t l
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
        when id_equal v I.combine_id && Effect.sub_effect e1 d2' ->
          (** applies when we have
           combine (combine a b) c
           and
           a is included in the intersection of a,b and c *)
          (** in this case return combine b c *)
          combine db t2 l
      | Some (v,([],[],[_;e2;e3]), b, _ )
        when id_equal v I.combine_id &&
          Effect.sub_effect (Effect.union e2 e3) (Effect.union d2' d3') ->
            combine b t2 l
      | _  ->
          simple_app2 (predef I.combine_id ([],[],[d1';d2';d3']) l) t1 t2 l

and restrict eff t l =
  let d = Effect.diff (domain t) eff in
  if Effect.is_empty d then t else
  try
    match destruct_app2_var t with
    | Some (v,([],[],[e1;_;e3]), m1, m2)
      when id_equal v I.combine_id  ->
        if Effect.sub_effect eff e3 then restrict eff m2 l
        else if Effect.sub_effect eff e1 then restrict eff m1 l
        else raise Exit
    | _ -> raise Exit
  with Exit -> simple_app (predef I.restrict_id ([],[],[d; eff]) l) t l

let applist ?(fix=`Prefix) l loc =
  match l with
  | [] | [ _ ] -> failwith "not enough arguments given"
  | [f;a;b] when fix = `Infix -> appi f a b loc
  | a::b::rest ->
      List.fold_left (fun acc x -> app acc x loc) (app a b loc) rest

let infer_app ?fix ?(regions=[]) ?(effects=[]) ?rty x tel l =
  let (tvl,rl,el),ty = x.scheme in
  let ty = Ty.elsubst el effects (Ty.rlsubst rl regions ty) in
(*
  Myformat.printf "inferring args for %a : ∀%a.  %a with args %a@."
  Name.print x Name.print_list tvl Ty.print ty (Myformat.print_list
  Myformat.space (fun fmt t ->
    Myformat.fprintf fmt "%a : %a" print t Ty.print t.t)) tel;
*)
  let tyl, xrty = Ty.nsplit ty in
  if List.length tyl <> List.length tel then invalid_arg "infer_app";
  let vars = List.fold_right Name.S.add tvl Name.S.empty in
  let matching = Ty.matching vars in
  let initial =
    match rty with
    | None -> Name.M.empty
    | Some rty -> matching Name.M.empty xrty rty in
  let s = List.fold_left2 matching initial tyl (List.map (fun t -> t.t) tel) in
  let tl = List.map (fun x -> Name.M.find x s) tvl in
  applist ?fix (var x (tl,regions,effects) l :: tel) l

let infer_predef ?fix ?regions ?effects ?rty id =
  let x,t = PL.var_and_type id in
  let x = mk_var_with_scheme x t in
  infer_app ?fix ?regions ?effects ?rty x

let le t1 t2 loc =
  simple_appi (spredef I.le_id loc) t1 t2 loc

let get_tuple_var tl i j l =
  (predef (I.get_tuple_id i j) (tl,[],[])) l

let destr_tuple i =
  assert (i>1);
  let rec aux k acc t =
    if k = 0 then
      match t.v with
      | Var (v,_) when id_equal v (I.mk_tuple_id i) -> Some acc
      | _ -> None
    else
      match t.v with
      | App (t1,t2,_,_) -> aux (k-1) (t2::acc) t1
      | _ -> None in
  aux i []

let get_tuple i t l =
  let n, tl =
    (** compute the length of the tuple along with the list of types, but take
       care of the singleton case. *)
    try
      let tl = Ty.tuple_list t.t in
      List.length tl, tl
    with Invalid_argument _ -> 1, [t.t] in
  if n = 1 then begin assert (i = 1); t end
  else
    begin match destr_tuple n t with
    | None -> app (get_tuple_var tl n i l) t l
    | Some l -> List.nth l (i-1)
    end

let encl lower i upper loc = and_ (le lower i loc) (le i upper loc) loc
let efflam x eff e = plam x (Ty.map eff) e
let lam x t p e q =
  mk_val (Lam (x,t,[],(p,e,q))) (Ty.arrow t e.t e.e)
let caplam x t cap p e q =
  mk_val (Lam (x,t,cap,(p,e,q))) (Ty.caparrow t e.t e.e cap)
let plus t1 t2 loc =
  infer_predef ~fix:`Infix I.plus_id [t1;t2] loc

let minus t1 t2 loc = appi (spredef I.minus_id loc) t1 t2 loc
let ref_get reg ref l = infer_predef I.refget_id [reg; ref] l

let one = mk_val (Const (Const.Int Big_int.unit_big_int)) Ty.int
let succ t loc = plus t (one loc) loc
let prev t loc = minus t (one loc) loc

let param t e = mk (Param (t,e)) t e

let mk_tuple n tl l =
  if n = 0 then void l
  else if n = 1 then List.hd tl
  else infer_predef (I.mk_tuple_id n) tl l

let mk_tuple tl = mk_tuple (List.length tl) tl

let mk_pair t1 t2 = mk_tuple [t1;t2]

let letreg l e = mk (LetReg (l,e)) e.t (Rw.rremove e.e l)
let andlist l loc =
  match l with
  | [] | [ _ ] -> failwith "not enough arguments given"
  | a::b::rest ->
      List.fold_left (fun acc x -> and_ acc x loc) (and_ a b loc) rest

let rec is_value x =
  match x.v with
  | Const _ | Var _ | Lam _ | PureFun _ | Quant _ | HoareTriple _ -> true
  | Let _ | Ite _ | LetReg _ | Param _ -> false
  | Gen (_,e) -> is_value e
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
  let var = mk_var_with_type v t in
  let tv = svar var loc in
  squant k v t (f tv) loc

let forall ?s t f loc = quant ?s `FA t f loc
let effFA ?s e f loc = forall ?s (Ty.map e) f loc
let plamho ?s t f loc =
  let v =
    match s with
    | None -> Name.new_anon ()
    | Some s -> Name.from_string s in
  let var = mk_var_with_type v t in
  let tv = svar var loc in
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
    when id_equal v I.restrict_id ->
      Some (map,e1,e2)
  | _ -> None

let destruct_get' x =
  match destruct_app2_var' x with
  | Some (v, ([t],[reg],[e]), r,map) when id_equal v I.get_id ->
      Some (t,r,reg,Effect.radd e reg,map)
  | _ -> None

let destruct_get x = destruct_get' x.v

let get ref map l =
  match ref.t with
  | Ty.Ref (r,t) ->
      let d = domain map in
      let d = Effect.rremove d [r] in
      simple_app2 (predef I.get_id ([t],[r],[d]) l) ref map l
  | _ -> assert false

let rec decl_map ?varfun ?termfun ?(declfun=ExtList.singleton) =
  let term_map = rebuild_map ?varfun ?termfun in
  fun d ->
    let d =
      match d with
      | Logic _ | TypeDef _ | DLetReg _ | DGen _ | Decl _ -> d
      | Formula (s,t,k) -> Formula (s,rebuild_map ?varfun ?termfun t, k)
      | Section (s,th,kind) ->
          Section (s,theory_map ?varfun ?termfun ~declfun th, kind)
      | Inductive (n,g,t,tel) -> Inductive (n,g,t, List.map term_map tel)
      | Program (n,g,t,r) -> Program (n,g,term_map t, r) in
    declfun d
and theory_map ?varfun ?termfun ?declfun th =
  List.flatten (List.map (decl_map ?varfun ?termfun ?declfun) th)

let mk_formula n f k =
  match f.v with
  | Const Const.Ptrue -> None
  | _ -> Some (Formula (n,f,k))

let mk_goal n f = mk_formula n f `Proved
