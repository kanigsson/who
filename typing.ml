open Vars
open Ast
open Ty
module SM = Misc.StringMap
module SS = Misc.StringSet

exception Error of string * Loc.loc

let error s loc = raise (Error (s,loc))

type env = 
  { types : (Generalize.t * Ty.t) Var.M.t; }

let add_var env x g t = 
  { types = Var.M.add x (g,t) env.types }
let add_svar env x t = 
  { types = Var.M.add x (Generalize.empty,t) env.types }


let type_of_var env x = Var.M.find x env.types

let ftype_of_var env x = 
  let m,t = type_of_var env x in
(*   Format.printf "ftype_of_var : %a of type %a@." Vars.var x Ty.print t; *)
  m, to_logic_type t

let prety eff = parr (map eff) prop
let postty eff t = parr (map eff) (parr (map eff) (parr t prop)) 

open Format
(* TODO hybrid environment *)
let rec formtyping' env loc = function
  | Ast.Const c -> Ty.const (Const.type_of_constant c)
  |Ast.Var (s,i) -> 
      begin try 
        let g, t = ftype_of_var env s in
        let r = Ty.allsubst g i t in
(*         printf "var : %a of type %a@." Vars.var s Ty.print r; r *)
        r
      with Not_found -> 
        error (Myformat.sprintf "unknown variable: %a" Var.print s) loc 
      end
  | Ast.App (e1,e2,_,_) ->
      let t1 = formtyping env e1 in
      let t2 = formtyping env e2 in
      begin match t1 with
      | C (Arrow _) -> error "effectful application not allowed in logic" loc
      | C (PureArr (ta,tb)) ->
          if Ty.equal ta t2 then tb else error "type mismatch" loc
      | _ -> error "no function type" loc
      end
  | TypeDef _ -> assert false
  | PureFun (x,t,e) -> parr t (formtyping (add_svar env x t) e)
  | Logic t -> t
  | Axiom f -> fis_oftype env prop f; prop
  | Quant (k,x,t,e) -> 
      fis_oftype (add_svar env x t) prop e;
      prop
  | Ite (e1,e2,e3) ->
      fis_oftype env prop e1;
      let t = formtyping env e2 in
      fis_oftype env t e3;
      t
  | Lam (x,t,p,e,q) ->
      let env = add_svar env x t in
      let t',eff = typing env e in
      pre env eff p;
      post env eff t' q;
      to_logic_type (arrow t t' eff)
  | Let (tl,e1,x,e2,r) ->
      let t = formtyping env e1 in
      let env = add_var env x tl t in
      let t = formtyping env e2 in
      t
  | Param _ -> error "effectful parameter in logic" loc
  | For _ -> assert false
  | Annot (e,t) -> fis_oftype env t e; t
  | LetReg _ -> assert false
and formtyping env (e : Ast.Recon.t) : Ty.t =
(*   Myformat.printf "formtyping %a@." Ast.Recon.print e; *)
  let t = formtyping' env e.loc e.v in
  if Ty.equal e.t t then
    if Effect.is_empty e.e then t
    else error (Myformat.sprintf "not empty: %a" Effect.print e.e) e.loc
  else
    error (Myformat.sprintf "fannotation mismatch: %a and %a@." 
             Ty.print e.t Ty.print t) e.loc
and pre env eff (_,x) =
  match x with
  | None -> ()
  | Some f -> fis_oftype env (prety eff) f
and post env eff t (_,_,x) =
  match x with
  | PNone -> ()
  | PPlain f -> fis_oftype env (postty eff t) f
  | _ -> assert false
and typing' env loc = function
  | Ast.Const c -> 
      Ty.const (Const.type_of_constant c), Effect.empty
  |Ast.Var (s,i) -> 
      begin try 
        let g, t = type_of_var env s in
        Ty.allsubst g i t, Effect.empty
      with Not_found -> 
        error (Myformat.sprintf "unknown variable: %a" Var.print s) loc
      end
  | Ast.App (e1,e2,_,_) ->
      let t1, eff1 = typing env e1 in
      let t2,eff2 = typing env e2 in
      let effi = Effect.union eff2 eff1 in
(*
      printf "app of %a and %a: eff1:%a eff2:%a@."
      Recon.print e1 Recon.print e2 Effect.print eff1 Effect.print eff2;
*)
      begin match t1 with
      | C (Arrow (ta,tb,eff)) -> 
          if ta = t2 then tb, Effect.union eff effi
          else error "type mismatch" loc
      | C (PureArr (ta,tb)) ->
          if Ty.equal ta t2 then tb, effi else error "type mismatch" loc
      | _ -> error "no function type" loc
      end
  | Lam (x,t,p,e,q) ->
      let env = add_svar env x t in
      let t',eff = typing env e in
      pre env eff p;
      post env eff t' q;
      arrow t t' eff, Effect.empty
  | Let (tl,e1,x,e2,r) ->
      let env' =
        match r with 
        | NoRec -> env
        | Rec t -> add_svar env x t in
      let t,eff1 = typing env' e1 in
      let env = add_var env x tl t in
      let t, eff2 = typing env e2 in
      t, Effect.union eff1 eff2
  | Param (t,e) -> t,e
  | TypeDef (tl,t,x,e) -> typing env e
  | PureFun (x,t,e) ->
      let env = add_svar env x t in
      let t', eff = typing env e in
      if Effect.is_empty eff then parr t t', eff
      else error "effectful pure function" loc
  | Quant (_,x,t,e) ->
      let env = add_svar env x t in
      let t', eff = typing env e in
      if Effect.is_empty eff && Ty.equal t' Ty.prop then Ty.prop, eff
      else error "not of type prop" loc
  | Axiom e -> formtyping env e, Effect.empty
  | Logic t -> t, Effect.empty
  | Annot (e,t) -> 
      let t', eff = typing env e in
      if Ty.equal t t' then t, eff else error "wrong type annotation" loc
  | Ite (e1,e2,e3) ->
      let t1, eff1 = typing env e1 in
      if Ty.equal t1 Ty.bool then
        let t2, eff2 = typing env e2 in
        let t3, eff3 = typing env e3 in
        if Ty.equal t2 t3 then 
          t2, Effect.union eff1 (Effect.union eff2 eff3)
        else error "mismatch on if branches" loc
      else error "condition is not of boolean type" loc
  | LetReg (vl,e) ->
      let t, eff = typing env e in
      t, Effect.rremove vl eff
  | For _ -> assert false

and typing env (e : Ast.Recon.t) : Ty.t * Effect.t =
(*   Myformat.printf "typing %a@." Ast.Recon.print e; *)
  let ((t',eff) as x) = typing' env e.loc e.v in
  if Ty.equal e.t t' then x else 
    error (Myformat.sprintf "annotation mismatch: %a and %a@." 
             Ty.print e.t Ty.print t') e.loc
and fis_oftype env t e =
  let t' = formtyping env e in
  if Ty.equal t t' then () 
  else 
    error 
      (Myformat.sprintf "typing mismatch: %a and %a" Ty.print t Ty.print t') 
      e.loc

let typing t = ignore (typing { types = Var.M.empty} t)
