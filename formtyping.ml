module A = Asttypes
module F = Formula
open Vars

exception Error of string * Loc.loc

let error s loc = raise (Error (s,loc))

let check_type env t loc = 
  if Fty.well_formed (fun v -> Penv.get_arity v env) t then ()
  else error (Error.illformed_fty t) loc


let type_of_var v el tl rl env = 
  let ts = Penv.get_f v env in
  Fty.Scheme.instance ts el tl rl

open Fty
let rec formula loc env = function
  | F.Const c -> Fty.const (Ty.type_of_constant c)
  | F.App (f1,f2,_) -> 
      let t2 = form_node env f2 in
      begin match form_node env f1 with
      | `U `Arr (ta,tb) when Fty.equal ta t2 -> tb
      | `U `Arr (ta,_) -> error (Error.fty_app_mismatch t2 ta) loc
      | t1 -> error (Error.fnot_a_function f1 t1) loc
      end
  | F.EvGen e -> 
      let l, f = F.open_evgen e in
      let env = Penv.add_evars l env in
      if form_node env f = Fty.prop then Fty.prop 
      else error Error.forall_ex_prop loc
  | F.RGen (b,tl) ->
      let rl, f = F.open_rbind b in
      let env = Penv.add_frvars (List.combine rl tl) env in
      if form_node env f = Fty.prop then Fty.prop 
      else error Error.forall_ex_prop loc
  | F.TyGen f -> 
      let l, f = F.open_tygen f in
      let env = List.fold_left (fun acc v -> Penv.add_type v 0 acc) env l in
      if form_node env f = Fty.prop then Fty.prop 
      else error Error.forall_ex_prop loc
  | F.Binder (k,argt,l) ->
      let v,f = F.open_bind l in
      let env = Penv.add_fvar v (Fty.Scheme.fty argt) env in
      begin match k, form_node env f with
        | A.Lam, ft -> Fty.arr argt ft
        | (A.FA | A.Ex) , (`U `Const A.TProp as ft) -> ft
        | _ -> error Error.forall_ex_prop loc
      end
  | F.Var (v,l,tl,rl) -> 
      begin try type_of_var v l tl rl env
      with 
      | Effect.IncompatibleSubst -> error Error.incompatible_subst loc
      | Not_found -> error (Error.unbound_id "logic" (Var.to_name v)) loc
      | Invalid_argument "List.fold_right2" -> error Error.effect_inst_nbr loc
      end
  | F.Empty -> Fty.mkmap Effect.empty
  | F.Get (r,m) ->
      begin match form_node env m with
        | `U `Map e ->
            if Effect.rmem r e then Penv.get_fr r env
            else error (Error.label_not_contain_r m r) loc
        | _ -> error (Error.not_a_label m) loc
      end
  | F.Set (r,f,m) -> 
      begin match form_node env m with
        | (`U `Map e) as t ->
            let ft = form_node env f in
            if Effect.rmem r e then 
              let rt = Penv.get_fr r env in
              if Fty.equal rt ft then t
              else error (Error.fty_app_mismatch rt ft) loc
            else error (Error.label_not_contain_r m r) loc
        | _ -> error (Error.not_a_label m) loc
      end
  | F.Restrict (eff,m) ->
      begin match form_node env m with
      | (`U `Map e) ->
          if Effect.is_subset eff e then Fty.mkmap eff
          else error (Error.effects_not_subset eff e) loc
      | _ -> error (Error.not_a_label m) loc
      end
  | F.Combine (m1,m2) ->
      begin match form_node env m1, form_node env m2 with
      | (`U `Map e1), (`U `Map e2) -> Fty.mkmap (Effect.union e1 e2)
      | _ -> error (Error.not_a_label m1) loc
      end
  | F.PolyLet (p, f) ->
      let g, v = F.open_letgen p in
      let x,f = F.open_bind f in
      let envgen = Penv.add_fgen g env in
      let vt = form_node envgen v in
      let env = Penv.add_fvar x (Fty.Scheme.close g vt) env in
      form_node env f
  | F.Let (f,b) ->
      let x,body = F.open_bind b in
      let t = form_node env f in
      let env = Penv.add_fvar x (Fty.Scheme.fty t) env in
      form_node env body

    and form_node env f =
    let t = formula f.F.loc env (F.get_sub f) in
    let oldt = F.get_type f in
    if Fty.equal t oldt then t else 
      failwith 
      (Misc.mysprintf "wrongly typed formula %a : annotated with %a but of type %a" 
        Formula.print f Fty.print oldt Fty.print t)

let pre_type eff = Fty.maparr eff Fty.prop
let post_type eff rt = Fty.maparr eff (Fty.maparr eff (Fty.arr rt Fty.prop)) 

let is_of_type env ft f = 
  match form_node env f with
  | t' when Fty.equal ft t' -> ()
  | t' -> error (Error.fty_form_mismatch t' ft) f.F.loc

 
let decl env = function
  | `Type (i,v) -> Penv.add_type v i env
  | `Goal (_,f) 
  | `Axiom (_,f) -> is_of_type env Fty.prop f ; env
  | `Logic (v,tl,ft) -> 
      Penv.add_fvar v (Fty.Scheme.close ([], tl,[]) ft) env
  | `Predicate (x,tl,f) ->
      let env' = Penv.sadd_tyvars tl env in
      let t = form_node env' f in
      Penv.add_fvar x (Fty.Scheme.close ([],tl,[]) t) env
  | `Param (v,gl,ft,f) -> 
      let env' = Penv.add_fgen gl env in
      let () = is_of_type env' ft f in
      let env = Penv.add_fvar v (Fty.Scheme.close gl ft) env in
      env
  | `Region l -> Penv.add_frvars l env

let allformula (l : Decl.F.t list)  =
  let env = List.fold_left decl Penv.empty Initdecl.decl in
  ignore (List.fold_left decl env l)

