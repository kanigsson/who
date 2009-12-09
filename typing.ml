open Ast
open Ty
module SM = Misc.StringMap
module SS = Misc.StringSet
module RS = Name.S

module G = Generalize

exception Error of string * Loc.loc

let error loc s = 
  Myformat.ksprintf (fun s -> raise (Error (s,loc))) s

type env = 
  { types : (G.t * Ty.t) Name.M.t; }

let add_var env x g t = 
  { types = Name.M.add x (g,t) env.types }
let add_svar env x t = 
  { types = Name.M.add x (G.empty,t) env.types }

let disjoint_union loc s1 s2 = 
  if RS.is_empty (RS.inter s1 s2) then RS.union s1 s2 
  else error loc "double effect"

let disj_union3 loc s1 s2 s3 = 
  disjoint_union loc (disjoint_union loc s1 s2) s3


let type_of_var env x = Name.M.find x env.types

let ftype_of_var env x = 
  let m,t = type_of_var env x in
(*   Format.printf "ftype_of_var : %a of type %a@." Vars.var x Ty.print t; *)
  m, to_logic_type t

let prety eff = parr (map eff) prop
let postty eff t = 
  parr (map eff) (parr (map eff) (parr (Ty.to_logic_type t) prop)) 

let set_list_contained l s =
  RS.for_all (fun x -> List.exists (fun y -> Name.equal x y) l) s

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
        error loc "unknown variable: %a" Name.print s
      end
  | Ast.App (e1,e2,_,_) ->
      let t1 = formtyping env e1 in
      let t2 = formtyping env e2 in
(*
      Myformat.printf "app of %a and %a of types %a and %a@."
      Recon.print e1 Recon.print e2 Ty.print t1 Ty.print t2;
*)
      begin match t1 with
      | C (Arrow _) -> error loc "effectful application not allowed in logic"
      | C (PureArr (ta,tb)) ->
          if Ty.equal ta t2 then tb else 
            (Myformat.printf "here@."; error loc "%s" (Error.ty_app_mismatch t2 ta))
      | _ -> error loc "no function type" 
      end
  | TypeDef (_,_,_,e) -> formtyping env e
  | PureFun (t,b) -> 
      let x,e = sopen b in
      parr t (formtyping (add_svar env x t) e)
  | Logic t -> t
  | Axiom f -> fis_oftype env prop f; prop
  | Quant (_,t,b) -> 
      let x,e = sopen b in
      fis_oftype (add_svar env x t) prop e;
      prop
  | Ite (e1,e2,e3) ->
      fis_oftype env prop e1;
      let t = formtyping env e2 in
      fis_oftype env t e3;
      t
  | Lam (x,t,cap,p,e,q) ->
      let env = add_svar env x t in
      let t',eff, capreal = typing env e in
      if not (set_list_contained cap capreal) then 
        error loc "wrong declaration of capacities on lambda";
      pre env eff p;
      post env eff t' q;
      to_logic_type (caparrow t t' eff cap)
  | Gen (_,e)-> formtyping env e
  | Let (_,g,e1,b,_) ->
      let x,e2 = sopen b in
(*       Myformat.printf "let: %a@." Name.print x; *)
      let t = formtyping env e1 in
      let env = add_var env x g t in
      let t = formtyping env e2 in
      t
  | Annot (e,t) -> fis_oftype env t e; t
  | Section (_,_,e) | EndSec e -> formtyping env e
  | Param _ -> error loc "effectful parameter in logic"
  | For _ -> assert false
  | LetReg _ -> assert false
and formtyping env (e : Ast.Recon.t) : Ty.t =
(*   Myformat.printf "formtyping %a@." Ast.Recon.print e; *)
  let t = formtyping' env e.loc e.v in
  if Ty.equal e.t t then
    if NEffect.is_empty e.e then t
    else error e.loc "not empty: %a" NEffect.print e.e
  else
    error e.loc "fannotation mismatch on %a: %a and %a@." 
      Ast.Recon.print e Ty.print e.t Ty.print t

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
      Ty.const (Const.type_of_constant c), NEffect.empty, RS.empty
  |Ast.Var (s,i) -> 
      begin try 
        let g, t = type_of_var env s in
        Ty.allsubst g i t, NEffect.empty, RS.empty
      with Not_found -> 
        error loc "unknown variable: %a" Name.print s
      end
  | Ast.App (e1,e2,_,capapp) ->
      let t1, eff1, cap1 = typing env e1 in
      let t2,eff2, cap2 = typing env e2 in
      let effi = NEffect.union eff2 eff1 in
(*
      printf "app of %a and %a: eff1:%a eff2:%a@."
      Recon.print e1 Recon.print e2 NEffect.print eff1 NEffect.print eff2;
*)
      begin match t1 with
      | C (Arrow (ta,tb,eff,caparg)) -> 
          if Ty.equal ta t2 then 
            if Misc.list_equal Name.compare capapp caparg then
              tb, NEffect.union eff effi, 
              disj_union3 loc cap1 cap2 (Name.list_to_set caparg)
            else 
              error loc "mismatch on creation permissions: expected %a, given %a"
                 Name.print_list caparg Name.print_list capapp
          else error loc "%s" (Error.ty_app_mismatch t2 ta)
      | C (PureArr (ta,tb)) ->
          if Ty.equal ta t2 then tb, effi, disjoint_union loc cap1 cap2 else 
            error loc "%s" (Error.ty_app_mismatch t2 ta) 
      | _ -> error loc "no function type"
      end
  | Lam (x,t,cap,p,e,q) ->
      let env = add_svar env x t in
      let t',eff,capreal = typing env e in
      if not (set_list_contained cap capreal) then 
        error loc "wrong declaration of capacities";
      pre env eff p;
      post env eff t' q;
      caparrow t t' eff cap, NEffect.empty, RS.empty
  | Let (_,g,e1,b,r) ->
      let x, e2 = sopen b in
(*       Myformat.printf "plet: %a@." Name.print x; *)
      if not ( G.is_empty g || Recon.is_value_node e1) then 
        error loc "generalization over non-value";
      let env' =
        match r with 
        | NoRec -> env
        | Rec t -> add_svar env x t in
      let t,eff1, cap1 = typing env' e1 in
      let env = add_var env x g t in
      let t, eff2, cap2 = typing env e2 in
      t, NEffect.union eff1 eff2, disjoint_union loc cap1 cap2
  | Param (t,e) -> t,e, RS.empty
  | TypeDef (_,_,_,e) -> typing env e
  | PureFun (t,b) ->
      let x,e = sopen b in
      let env = add_svar env x t in
      let t', eff, cap = typing env e in
      if NEffect.is_empty eff && RS.is_empty cap then parr t t', eff, cap
      else error loc "effectful pure function"
  | Quant (_,t,b) ->
      let x, e = sopen b in
      let env = add_svar env x t in
      let t', eff, cap = typing env e in
      if NEffect.is_empty eff && RS.is_empty cap && Ty.equal t' Ty.prop 
      then Ty.prop, eff, cap
      else error loc "not of type prop"
  | Axiom e -> formtyping env e, NEffect.empty, RS.empty
  | Logic t -> t, NEffect.empty, RS.empty
  | Annot (e,t) -> 
      let t', eff, cap = typing env e in
      if Ty.equal t t' then t, eff, cap else error loc "wrong type annotation"
  | Section (_,_,e) | EndSec e -> typing env e
  | Ite (e1,e2,e3) ->
      let t1, eff1, cap1 = typing env e1 in
      if Ty.equal t1 Ty.bool then
        let t2, eff2, cap2 = typing env e2 in
        let t3, eff3, cap3 = typing env e3 in
        if Ty.equal t2 t3 then 
          t2, NEffect.union eff1 (NEffect.union eff2 eff3),
          disj_union3 loc cap1 cap2 cap3
        else error loc "mismatch on if branches"
      else error loc "condition is not of boolean type"
  | LetReg (vl,e) ->
      let t, eff, cap = typing env e in
      t, NEffect.rremove eff vl, Name.remove_list_from_set vl cap
  | For _ -> assert false
  | Gen _ -> assert false

and typing env (e : Ast.Recon.t) : Ty.t * NEffect.t * RS.t =
(*   Myformat.printf "typing %a@." Ast.Recon.print e; *)
  let ((t',_,_) as x) = typing' env e.loc e.v in
  if Ty.equal e.t t' then x else 
    error e.loc "annotation mismatch on %a: %a and %a@." 
      Ast.Recon.print e Ty.print e.t Ty.print t'
and fis_oftype env t e =
  let t' = formtyping env e in
  if Ty.equal t t' then () 
  else 
    error e.loc "typing mismatch on %a: expected %a but is %a" 
      Ast.Recon.print e Ty.print t Ty.print t' 

let typing t = ignore (typing { types = Name.M.empty} t)

let formtyping t = ignore (formtyping {types = Name.M.empty} t)
