open Ast
open Recon
open Vars
module F = Formula
module M = Myformat

exception Error of string * Loc.loc
let error s loc = raise (Error (s,loc))

let var v = Var.from_name v
let ty t = Fty.from_ty (Ty.to_logic_type t)

let rec lift_value _ = assert false

(*
  let l = v.loc in
  match v.v with
  | Var _ | Const _ | Logic _ -> v
  | App (v1,v2,kind,_) -> 
      M.printf "app@.";
      app ~kind (lift_value v1) (lift_value v2) l
  | Lam (x,t,p,e,q) ->
      M.printf "lam@.";
      let t = Ty.to_logic_type t in
      let _,p = p and _,_,q = q in
      let p = 
        match p with 
        | None -> plam x t (efflam_ho e.e (fun _ -> ptrue_ l) l) l
        | Some p -> plam x t p l 
      and q = 
        match q with
        | PResult _ -> assert false
        | PNone ->
            plam x t (
              efflam_ho e.e (fun m -> 
                efflam_ho e.e (fun m2 -> 
                  plam_ho (Ty.to_logic_type e.t) (fun r ->
                    ptrue_ l) l) l) l) l
        | PPlain q -> plam x t q l in
      mk_tuple p q l
  | PureFun (x,t,v) -> 
      M.printf "purefun@.";
      plam x t (lift_value v) l
  | _ -> 
      error (Myformat.sprintf "not a value: %a" print v) l
*)

let rec correct v = 
  let l = v.loc in
  match v.v with
  | Var _ | Const _ -> F.true_ l
  | App (v1,v2,_,_) -> F.and_ (correct v1) (correct v2) l
  | Lam (x,t,p,e,q) -> 
      let lt = Fty.from_ty (Ty.to_logic_type t) in
      F.effFAho (Fty.from_eff e.e) (fun r ->
        F.forall (Var.from_name x) lt
          (F.impl 
            (match p with 
              | _,None -> F.true_ l
              | _,Some f -> F.app (to_formula f) r l)
            (wp_node r 
              (match q with 
                | _,_,PNone -> F.lamho (ty e.t) (fun _ -> F.true_ l) l
                | _,_,PResult _ -> assert false
                | _,_,PPlain f -> F.app (to_formula f) r l) 
              e) l) l) l
  | PureFun (x,t,e) -> F.forall (Var.from_name x) (ty t) (correct e) l
  | _ -> assert false
and formula e = 
  let l = e.loc in
  match e.v with
  | Var (v,i) -> 
      F.var (Var.from_name v) 
        (Inst.map Fty.from_ty RVar.from_name Fty.from_eff i) 
        (Fty.from_ty e.t) l
  | Const c -> F.const c l
  | App (e1,e2,kind,_) -> F.app ~kind (formula e1) (formula e2)
  | Quant (k,x,t,e) -> F.varbind k (var x) (ty t) (formula e)
  | PureFun (x,t,e) -> F.varbind `LAM (var x) (ty t) (formula e)
  | Let (g,e1,x,e2,NoRec) -> 
      F.polylet_

      of Ty.Generalize.t * ('a,'b,'c) t' * Name.t * ('a,'b,'c) t' * isrec
  | Axiom _ | Logic _ | Annot _ | TypeDef _ -> assert false
  | Param _ | For _ | LetReg _ -> 
(*   | Ite of ('a,'b,'c) t' * ('a,'b,'c) t' * ('a,'b,'c) t' *)
  | _ -> assert false
and wp_node _ _ _ = assert false
      
(*

and wp_node m q e = 
  let t = e.t and _ = e.e and l = e.loc in
  if is_value_node e then
    and_ (applist [q;m;lift_value e] l) (correct e) l
  else
    match e.v with
    | Const _ | Var _ | Lam _ | PureFun _ | For _ | Annot _ -> 
        assert false
    | Axiom t -> axiom t l
    | Logic t -> logic t l
    | TypeDef (g,t,x,e) -> typedef g t x (wp_node m q e) l
    | Quant (k,x,t,e) -> squant k x t (wp_node m q e) l 
    | Ite (v,e1,e2) ->
        ite (eq (lift_value v) (btrue_ l) l)
              (wp_node m e1 q) (wp_node m e2 q) l
    | LetReg (r,e) -> letreg r (wp_node m e q) l
    | Param (t,_) -> ptrue_ l
    | App (v1,v2,f,_) ->
        let lv1 = lift_value v1 and lv2 = lift_value v2 in
        andlist 
          [ correct v1; correct v2;
            applist [pre lv1 l; lv2; m ] l;
            effFA e.e (fun m2 ->
              forall (Ty.to_logic_type t) (fun x ->
                impl (applist [post lv1 l; lv2; m; m2; x] l) 
                     (applist [q; m2; x] l) l) l) l
          ] l
    | Let (g,({v = (Axiom _ | Logic _) } as v),x,e2,r) ->
        let_ g v x (wp_node m q e2) r l
    | Let (g,e1,x,e2,r) ->
        if is_value_node e1 then
          let lv = lift_value e1 in
          and_ (correct e1) 
            (let_ g lv x (wp_node m q e2) NoRec l) l
        else
          wp_node m 
            (efflam_ho e1.e 
              (fun m2 -> 
                plam x (Ty.to_logic_type e1.t)
                  (wp_node m2 q e2) l) l) e1



let main e = 
  let l = e.loc in
  effFA e.e (fun m -> 
    wp_node m 
      (efflam_ho e.e (fun _ -> 
        plam_ho Ty.unit (fun x -> ptrue_ l) l) l) e) l
*)
