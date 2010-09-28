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

(** TODO error handling *)
module G = Ty.Generalize
module PL = Predefined
module I = Identifiers

type var = {
  var : Name.t;
  scheme : Ty.scheme ;
  is_constr : bool;
  fix : [ `Infix | `Prefix ]
}

type node =
  | Const of Const.t
  | Var of var * inst
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t
  | Lam of Name.t * Ty.t * funcbody
  | Let of G.t * t * t Name.bind
  | LetRec of G.t * Ty.t * (t * t) Name.bind
  | PureFun of Ty.t * t Name.bind
  | Ite of t * t * t
  | Quant of [`FA | `EX ] * Ty.t * t Name.bind
  | Param of Ty.t * Rw.t
  | Gen of G.t *  t
  | HoareTriple of funcbody
  | LetReg of Name.t list * t
  | Case of t * branch list
  | SubEff of t * Rw.t
and t = { v : node ; t : Ty.t ; e : Rw.t; loc : Loc.loc }
and isrec = Ty.t Const.isrec
and funcbody = t * t * t
and inst = (Ty.t, Name.t, Effect.t) Inst.t
and branch = (pattern * t) Name.listbind
and pattern_node =
  | PVar of Name.t
  | PApp of var * inst * pattern list
and pattern = { pv : pattern_node ; ploc : Loc.loc ; pt : Ty.t }

type decl =
  | Logic of Name.t * Ty.scheme
  | Formula of Name.t * t * [ `Proved | `Assumed ]
  | Section of Name.t *  decl list * section_kind
  | TypeDef of Name.t * Name.t list * typedef
  | Program of Name.t * G.t * t * isrec
  | Inductive of Name.t * G.t * Ty.t * inductive_branch list
  | DLetReg of Name.t list
  | DGen of G.t
  | Decl of string
and section_kind = [ `Block of Const.takeover list | `Structure ]
and typedef =
  | Abstract
  | ADT of constbranch list
and constbranch = Name.t * Ty.t list
and inductive_branch = Name.t * t

type theory = decl list

let varmap ~varfun ~tyfun v =
  let (g,t) = v.scheme in
  { var = varfun v.var ; scheme = g, tyfun t ;
    is_constr = v.is_constr ; fix = v.fix}

let map ~varfun ~varbindfun ~patternbindfun
        ~recbindfun ~tyfun ~rvarfun ~effectfun f =
  let rec aux' = function
    | (Const _ ) as t -> t
    | Param (t,e) -> Param (tyfun t, rwfun e)
    | Var (v,i) ->
        Var (varmap ~tyfun ~varfun v, Inst.map tyfun rvarfun effectfun i)
    | App (t1,t2) -> App (aux t1, aux t2)
    | Lam (x,t,b) -> Lam (x,tyfun t, body b )
    | LetReg (l,e) -> LetReg (l,aux e)
    | HoareTriple b -> HoareTriple (body b)
    | Let (g,e1,b) -> Let (g,aux e1,varbindfun b)
    | LetRec (g,t,b) -> LetRec (g,tyfun t, recbindfun b)
    | PureFun (t,b) -> PureFun (tyfun t, varbindfun b)
    | Ite (e1,e2,e3) -> Ite (aux e1, aux e2, aux e3)
    | Quant (k,t,b) -> Quant (k,tyfun t,varbindfun b)
    | Gen (g,e) -> Gen (g,aux e)
    | Case (t,bl) -> Case (aux t, List.map branch bl)
    | SubEff (t,rw) -> SubEff (aux t, rwfun rw)
  and rwfun e = Rw.map effectfun e
  and body (p,e,q) = aux p, aux e, aux q
  and branch b = patternbindfun b
  and aux t = {t with v = aux' t.v; t = tyfun t.t; e = rwfun t.e} in
  aux f

let refresh s t =
  map ~varfun:(Name.refresh s)
    ~varbindfun:(Name.refresh_bind s)
    ~patternbindfun:(Name.refresh_listbind s)
    ~recbindfun:(Name.refresh_bind s)
    ~tyfun:Misc.id
    ~rvarfun:Misc.id
    ~effectfun:Misc.id t

let pattern_map ~varfun ~tyfun ~rvarfun ~effectfun p =
  let varf = varmap ~varfun ~tyfun in
  let rec aux' p =
    match p with
    | PVar v -> PVar (varfun v)
    | PApp (v,i,pl) ->
        PApp (varf v,Inst.map tyfun rvarfun effectfun i, List.map aux pl)
  and aux p = { p with pv = aux' p.pv ; pt = tyfun p.pt } in
  aux p

let vopen = Name.open_bind refresh
let close = Name.close_bind
let vopen_with x = Name.open_with refresh x

let pattern_refresh s =
  pattern_map ~varfun:(Name.refresh s)
    ~tyfun:(Misc.id) ~rvarfun:Misc.id ~effectfun:Misc.id

let rec_refresh s (t1,t2) = refresh s t1, refresh s t2

let popen pb =
  let nvl, (p,t) =
    Name.open_listbind (fun s (p,t) -> pattern_refresh s p, refresh s t) pb in
  nvl, p, t

let pclose nvl p t = Name.close_listbind nvl (p,t)

let recopen b =
  let v,(t1,t2) = Name.open_bind rec_refresh b in
  v, t1, t2

let recclose v t1 t2 =
  Name.close_bind v (t1,t2)

let var_equal v1 v2 =
  Name.equal v1.var v2.var && Ty.scheme_equal v1.scheme v2.scheme

let rec equal' a b =
  match a, b with
  | Const c1, Const c2 -> Const.compare c1 c2 = 0
  | Var (v1,i1), Var (v2,i2) ->
      var_equal v1 v2 &&
      Inst.equal Ty.equal Name.equal Effect.equal i1 i2
  | App (a1,b1), App (a2,b2) -> equal a1 a2 && equal b1 b2
  | Gen (g1,t1), Gen (g2,t2) ->
      G.equal g1 g2 && equal t1 t2
  | Ite (a1,b1,c1), Ite (a2,b2,c2) -> equal a1 a2 && equal b1 b2 && equal c1 c2
  | Let (g1,ea1,b1), Let (g2,ea2,b2) ->
      G.equal g1 g2 && equal ea1 ea2 && bind_equal b1 b2
  | PureFun (t1,b1), PureFun (t2,b2) -> Ty.equal t1 t2 && bind_equal b1 b2
  | Quant (k1,t1,b1), Quant (k2,t2,b2) ->
      k1 = k2 && Ty.equal t1 t2 && bind_equal b1 b2
  | Lam (x1,t1,b1), Lam (x2,t2,b2) ->
      Name.equal x1 x2 && Ty.equal t1 t2 && funcbody_equal b1 b2
  | LetReg _, _ | Param _, _
  | Lam _, _ -> assert false
  | _, _ -> false
and bind_equal b1 b2 =
  (let x,eb1 = vopen b1 in
   let eb2 = vopen_with x b2 in
   equal eb1 eb2)
and funcbody_equal (p1,e1,q1) (p2,e2,q2) =
  equal p1 p2 && equal e1 e2 && equal q1 q2
and equal a b = equal' a.v b.v

let id_equal v id = PL.equal v.var id

let destruct_app' = function
  | App (f1,f2) -> Some (f1,f2)
  | _ -> None

let destruct_app2 = function
  | App ({v = App (f1,f2)},f3) -> Some (f1,f2,f3)
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

let lambda_rev_destruct =
  let rec aux acc t =
    match t.v with
    | PureFun (at,b) ->
        let x, f = vopen b in
        aux ((x,at)::acc)  f
    | _ -> acc, t in
  aux []

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
    | Const.NoRec -> Const.NoRec
    | Const.Rec t -> Const.Rec (ty env t)
  let add_id = Name.Env.add_id
  let add_ids = Name.Env.add_id_list

  let rec t env term =
    match destruct_get term with
    | Some (_,r,_,_,map) -> P.Get ( t env r,t env map)
    | None ->
        match term.v with
        | Const c -> P.Const c
        | Param (t,e) -> P.Param (ty env t, rw env e)
        | Var (v,(_,rl,_)) when id_equal v I.ref_id ->
            P.PRef (id env (List.hd rl))
        | Var (v,i) ->
            let s = id env v.var in
            P.Var (s, inst env i, ty env term.t,v.fix)
        | App (t1,t2) ->
            P.App (t env t1, t env t2)
        | LetReg (l,e) ->
            let env = add_ids env l in
            P.LetReg (List.map (id env) l,t env e)
        | Lam (x,at,b) ->
            let env = add_id env x in
            P.Lam (id env x,ty env at, body env b )
        | HoareTriple b -> P.HoareTriple (body env b)
          | PureFun (at,b) ->
            let x,e = vopen b in
            let env = add_id env x in
            P.PureFun (id env x, ty env at, t env e )
        | Quant (k,at,b) ->
            let x,e = vopen b in
            let env = add_id env x in
            P.Quant (k,id env x, ty env at,t env e)
        | Let (g,e1,b) ->
            let x, e2 = vopen b in
            let env', g = gen env g in
            let e1 = t env' e1 in
            let env = add_id env x in
            P.Let (g,e1,id env x, t env e2, Const.NoRec)
        | LetRec (g,targ,b) ->
            let x, e1,e2 = recopen b in
            let env = add_id env x in
            let env', g = gen env g in
            let e1 = t env' e1 in
            P.Let (g,e1,id env x, t env e2, Const.Rec (ty env targ))
        | Ite (e1,e2,e3) -> P.Ite (t env e1, t env e2, t env e3)
        | Gen (g,e) ->
            let env, g = gen env g in
            P.Gen (g,t env e)
        | Case (e,bl) ->
            let e = t env e in
            P.Case (e, List.map (branch env) bl)
        | SubEff (e,eff) ->
            P.SubEff (t env e,ty env e.t, rw env eff)
  and body env (t1,t2,t3) = t env t1, t env t2, t env t3
  and branch env pb =
    let nvl, p,e = popen pb in
    let env = add_ids env nvl in
    pattern env p, t env e
  and pattern env p =
    match p.pv with
    | PVar v -> P.PVar (id env v)
    | PApp (v,i,pl) ->
        P.PApp (id env v.var, inst env i, List.map (pattern env) pl)

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
    | TypeDef (n, tl, def) ->
        let env = add_id env n in
        let env' = add_ids env tl in
        let n = id env n and tl = List.map (id env') tl in
        let env, k =
          match def with
          | Abstract -> env, P.Abstract
          | ADT bl ->
              let env, bl = ExtList.fold_map (constbranch env') env bl in
              env, P.ADT bl in
        env, P.TypeDef (n,tl, k)
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
          List.map (ty env') args, List.map (ind_branch env') tl)
  and constbranch inner outer (n,tl) =
    let env = add_id outer n in
    env, (id outer n, List.map (ty inner) tl)
  and ind_branch env (n,b) =
    let env = add_id env n in
    id env n, t env b
  and theory env th =
    ExtList.fold_map decl env th


end
module Print = struct

  let predef kind =
    match kind with
    | `Who -> Name.M.empty
    | `Why3 -> Name.M.empty
    | `Coq -> Predefined.coq_map ()
    | `Pangoline -> Predefined.pangoline_map ()

  let empty ?(kind=`Who) () = Name.Env.empty (predef kind)

  let term ?kind fmt t =
    PrintTree.Print.term ?kind fmt (Convert.t (empty ?kind ()) t)

  let decl ?kind fmt d =
    let _, d = Convert.decl (empty ?kind ()) d in
    PrintTree.Print.decl ?kind fmt d

  let theory ?kind fmt th =
    let _, th = Convert.theory (empty ?kind ()) th in
    PrintTree.Print.theory ?kind fmt th

end

module Branch = struct
  let open_ = popen
  let close = pclose

  let term b =
    let _,_,t = open_ b in t

  let rw b =
    (* dirty code to access the effect of t without reopening *)
    let _,_,(_,t) = b in
    t.e

  let ty b =
    (* dirty code to access the type of t without reopening *)
    let _,_,(p,t) = b in
    p.pt, t.t

  let check exp_pty exp b =
    let pt, t = ty b in
    if Ty.equal exp t then ()
    else begin
      Myformat.printf "type mismatch in branch:expected type %a but is of type
      %a@." Ty.print exp Ty.print t;
      invalid_arg "check_branch"
    end;
    if Ty.equal exp_pty pt then ()
    else begin
      Myformat.printf "type mismatch: term is of type %a but pattern is of type
      %a@." Ty.print exp_pty Ty.print pt;
      invalid_arg "check_branch"
    end

end

module N = Name

let open_close_map ~varfun ~tyfun ~rvarfun ~effectfun t =
  let rec aux t =
    map ~varfun
      ~varbindfun:(fun b -> let x,f = vopen b in close x (aux f))
      ~recbindfun:(fun b ->
        let x, e1, e2 = recopen b in recclose x (aux e1) (aux e2))
      ~patternbindfun:(fun pb ->
        let nvl, p,t = popen pb in pclose nvl (pattern p) (aux t))
      ~tyfun ~rvarfun ~effectfun t
  and pattern p = pattern_map ~varfun ~tyfun ~rvarfun ~effectfun p in
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
let mk_var_with_scheme is_constr fix v s =
  { var = v; scheme = s ; is_constr = is_constr ; fix = fix }
let mk_var_with_type is_constr fix v t =
  { var = v; scheme = Ty.as_scheme t; is_constr = is_constr; fix = fix }
let simple_var_id s =
  let x, (g,t,f) = PL.var_and_type s in
  simple_var (mk_var_with_scheme false f x (g,t)) t

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
  let x, (g,t, fix) = PL.var_and_type s in
  let v = mk_var_with_scheme false fix x (g,t) in
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
  let rt = e2.t in
  let eff = Rw.union e1.e e2.e in
  match r with
  | Const.Rec t ->
      mk (LetRec (g, t, recclose x e1 e2)) rt eff l
  | _ ->
      true_or e2 (mk (Let (g, e1,Name.close_bind x e2)) rt eff l)

let plam x t e loc =
  mk_val (PureFun (t,Name.close_bind x e)) (Ty.parr t e.t) loc

let hoare_triple p e q l = mk_val (HoareTriple (p,e,q)) Ty.prop l

let subeff t e l =
  if Rw.sub t.e e then mk (SubEff (t,e)) t.t e l
  else begin
    Myformat.printf "subeffecting not correct@.";
    failwith "subeff"
  end

let gen g e l = true_or e (mk (Gen (g, e)) e.t e.e l)

let simple_app t1 t2 l =
  try
    let t = Ty.result t1.t and e = Ty.latent_effect t1.t in
    if not (Ty.equal (Ty.arg t1.t) t2.t) then raise Exit;
    mk (App (t1,t2)) t (Rw.union3 t1.e t2.e e) l
  with
  | Exit ->
      Myformat.printf "type mismatch on application: function %a has type %a,
        and argument %a has type %a@." print t1 Ty.print t1.t
        print t2 Ty.print t2.t ;
      invalid_arg "app"
  | Invalid_argument _ ->
      Myformat.printf "not a function: %a of type %a.." print t1 Ty.print t1.t;
      invalid_arg "app"


let simple_app2 t t1 t2 loc =
  simple_app (simple_app t t1 loc) t2 loc

let simple_eq t1 t2 l =
  simple_app2 (predef I.equal_id ([t1.t],[],[]) l) t1 t2 l

let get_tuple_var tl i j l =
  (predef (I.get_tuple_id i j) (tl,[],[])) l

let lam x t p e q =
  mk_val (Lam (x,t,(p,e,q))) (Ty.arrow t e.t e.e)

let case e bl l =
  let rw =
    List.fold_left (fun acc b ->
      Rw.union acc (Branch.rw b)) Rw.empty bl in
  let rw = Rw.union rw e.e in
  let t =
    match bl with
    | [] -> assert false
    | b::_ ->
        let _,exp_type = Branch.ty b in
        List.iter (Branch.check e.t exp_type) bl; exp_type in
  let pt = ptrue_ l in
  let terms = List.map Branch.term bl in
  if List.for_all (equal pt) terms then pt
  else mk (Case (e,bl)) t rw l


let mk_pattern p t l = { pv = p; pt = t; ploc = l }

let mk_pvar v t l =
  (** constructors are always applications in patterns, possibly to the empty
     pattern list *)
  mk_pattern (PVar v) t l

let mk_papp v i tl l =
  assert (v.is_constr);
  try
    let g,t = v.scheme in
    let nt = (Ty.allsubst g i t) in
    let tyl, rt = Ty.nsplit nt in
    List.iter2 (fun t e -> assert (Ty.equal t e.pt)) tyl tl;
    mk_pattern (PApp (v,i,tl)) rt l
  with Invalid_argument _ ->
    failwith (Myformat.sprintf "%a : not the right number of
    instantiations" Name.print v.var)

let destr_tuple i =
  assert (i>1);
  let rec aux k acc t =
    if k = 0 then
      match t.v with
      | Var (v,_) when id_equal v (I.mk_tuple_id i) -> Some acc
      | _ -> None
    else
      match t.v with
      | App (t1,t2) -> aux (k-1) (t2::acc) t1
      | _ -> None in
  aux i []

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

let rec app t1 t2 l : t =
(*     Myformat.printf "app: %a and %a@." print t1 print t2; *)
    try match t1.v with
    (* we are trying to build (λx.t) e, reduce to t[x|->e] *)
    | PureFun (_,l) ->
        let x, body = vopen l in
        subst x (fun _ -> t2) body
    (* double application, check if we are not in a simplification case *)
    | App (op,t1) ->
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
        | Some (v, _) ->
            begin match PL.is_get_tuple_var v.var with
            | None -> raise Exit
            | Some i -> get_tuple i t2 l
            end
        | _ -> raise Exit
    with Exit -> simple_app t1 t2 l

and app2 t t1 t2 loc = app (app t t1 loc) t2 loc
and appn t tl loc = List.fold_left (fun acc t -> app acc t loc) t tl

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
            app2 (v i l) arg1 arg2 l
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
      | Var (v,i) -> varfun v.var (inst i) t
      | App (t1,t2) -> app (aux t1) (aux t2) l
      | Let (g,e1,b) ->
          let x,f = vopen b in
          let_ g (aux e1) x (aux f) Const.NoRec l
      | LetRec (g,t,b) ->
          let x,e1,e2 = recopen b in
          let_ g (aux e1) x (aux e2) (Const.Rec t) l
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
      | Case (e,bl) -> case (aux e) (List.map branch bl) l
      | Lam (x,t,(p,e,q)) -> lam x t (aux p) (aux e) (aux q) l
      | SubEff (t,e) -> subeff (aux t) e l
      | LetReg _ | Param _ -> assert false in
    termfun t
  and branch b =
    let nvl, p,t = popen b in
    pclose nvl (pattern p) (aux t)
  and inst i = Inst.map tyfun Misc.id Misc.id i
  and pattern p =
    let l = p.ploc in
    match p.pv with
    | PVar v -> mk_pvar v (tyfun p.pt) l
    | PApp (v,i,pl) -> mk_papp v i (List.map pattern pl) l in
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
    | _ -> simple_app2 (spredef I.impl_id l) h1 goal l

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
  | _ -> simple_app2 (spredef I.and_id l) t1 t2 l

and or_ t1 t2 l =
  match t1.v,t2.v with
  | Const Const.Ptrue, _ -> t1
  | _, Const Const.Ptrue -> t2
  | Const Const.Pfalse, _ -> t2
  | _, Const Const.Pfalse -> t1
  | _ -> simple_app2 (spredef I.or_id l) t1 t2 l
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
and get_tuple i t l =
  let n, tl =
    (** compute the length of the tuple along with the list of types, but take
       care of the singleton case. *)
    try
      let tl = Ty.tuple_list t.t in
      List.length tl, tl
    with Invalid_argument _ -> 1, [t.t] in
  if n = 1 then begin assert (i = 1); t end
  else begin
    match destr_tuple n t with
    | None ->
        simple_app (get_tuple_var tl n i l) t l
    | Some l ->
        let r = List.nth l (i-1) in
        r
  end


let applist l loc =
  match l with
  | [] | [ _ ] -> failwith "not enough arguments given"
  | a::b::rest ->
      List.fold_left (fun acc x -> app acc x loc) (app a b loc) rest

let infer_app ?(regions=[]) ?(effects=[]) ?rty x tel l =
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
  applist (var x (tl,regions,effects) l :: tel) l

let infer_predef ?regions ?effects ?rty id =
  let x,(g,t,f) = PL.var_and_type id in
  let x = mk_var_with_scheme false f x (g,t) in
  infer_app ?regions ?effects ?rty x

let le t1 t2 loc =
  simple_app2 (spredef I.le_id loc) t1 t2 loc

let encl lower i upper loc = and_ (le lower i loc) (le i upper loc) loc
let efflam x eff e = plam x (Ty.map eff) e
let plus t1 t2 loc =
  infer_predef I.plus_id [t1;t2] loc

let minus t1 t2 loc = app2 (spredef I.minus_id loc) t1 t2 loc
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
  | Let _ | Ite _ | LetReg _ | Param _ | Case _ | LetRec _ | SubEff _ -> false
  | Gen (_,e) -> is_value e
  | App (t1,_) ->
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
  let var = mk_var_with_type false `Prefix v t in
  let tv = svar var loc in
  squant k v t (f tv) loc

let forall ?s t f loc = quant ?s `FA t f loc
let effFA ?s e f loc = forall ?s (Ty.map e) f loc
let plamho ?s t f loc =
  let v =
    match s with
    | None -> Name.new_anon ()
    | Some s -> Name.from_string s in
  let var = mk_var_with_type false `Prefix v t in
  let tv = svar var loc in
  plam v t (f tv) loc

let efflamho ?s e f loc = plamho ?s (Ty.map e) f loc

let rec is_param e =
  match e.v with
  | Param _ -> true
  | Lam (_,_,(_,e,_)) -> is_param e
  | PureFun (_,(_,_,e)) -> is_param e
  | _ -> false

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
      | Inductive (n,g,t,tel) ->
          Inductive (n,g,t, List.map (fun (x,b) -> x, term_map b) tel)
      | Program (n,g,t,r) -> Program (n,g,term_map t, r) in
    declfun d
and theory_map ?varfun ?termfun ?declfun th =
  List.flatten (List.map (decl_map ?varfun ?termfun ?declfun) th)

let mk_formula n f k =
  match f.v with
  | Const Const.Ptrue -> None
  | _ -> Some (Formula (n,f,k))

let mk_goal n f = mk_formula n f `Proved
