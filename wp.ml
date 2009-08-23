open Ast
open Recon
module F = Formula
module M = Myformat

exception Error of string * Loc.loc
let error s loc = raise (Error (s,loc))

let var v = Name.from_name v
let tyvar v = Name.from_name v
let rvar v = Name.from_name v
let effvar v = Name.from_name v
let ty t = Fty.from_ty (Ty.to_logic_type t)
let effect = Fty.from_eff 

let gen (tl,rl,el) = 
  (List.map tyvar tl, List.map rvar rl, List.map effvar el)
let gen_restrict (tl,_,_) = List.map tyvar tl

let rec lift_value v = 
  let l = v.loc in
  match v.v with
  | Name _ | Const _ | Logic _ -> formula v
  | App (v1,v2,kind,_) -> F.app ~kind (lift_value v1) (lift_value v2) l
  | PureFun (x,t,e) -> F.lam (var x) (ty t) (lift_value e) l
  | Lam (x,t,p,e,q) ->
      let t = ty t in
      let ef = effect e.e in
      let _,p = p and _,_,q = q in
      let p = 
        match p with 
        | None -> F.lam (var x) t (F.efflamho ef (fun _ -> F.true_ l) l) l
        | Some p -> F.lam (var x) t (formula p) l 
      and q = 
        match q with
        | PResult _ -> assert false
        | PNone ->
            F.lam (var x) t (
              F.efflamho ef (fun _ -> 
                F.efflamho ef (fun _ -> 
                  F.lamho (ty e.t) (fun _ -> F.true_ l) l) l) l) l
        | PPlain q -> F.lam (var x) t (formula q) l in
      F.tuple p q l
  | _ -> 
      error (Myformat.sprintf "not a value: %a" print v) l

and correct v = 
  let l = v.loc in
  match v.v with
  | Name _ | Const _ -> F.true_ l
  | App (v1,v2,_,_) -> F.and_ (correct v1) (correct v2) l
  | Lam (x,t,p,e,q) -> 
      let lt = ty t in
      F.effFAho (Fty.from_eff e.e) (fun r ->
        F.forall (var x) lt
          (F.impl 
            (match p with 
              | _,None -> F.true_ l
              | _,Some f -> F.app (formula f) r l)
            (wp_node r 
              (match q with 
                | _,_,PNone -> 
                    F.efflamho (effect e.e) (fun _ ->
                      F.lamho (ty e.t) (fun _ -> F.true_ l) l) l
                | _,_,PResult _ -> assert false
                | _,_,PPlain f -> F.app (formula f) r l) 
              e) l) l) l
  | PureFun (x,t,e) -> F.forall (var x) (ty t) (correct e) l
  | _ -> assert false
and formula e = 
  let l = e.loc in
  match e.v with
  | Name (v,i) -> 
      F.var (Name.from_name v) (Inst.map ty rvar effect i) (ty e.t) l
  | Const c -> F.const c l
  | App (e1,e2,kind,_) -> F.app ~kind (formula e1) (formula e2) l
  | Quant (k,x,t,e) -> 
      F.varbind (k :> [`EX | `FA | `LAM ]) (var x) (ty t) (formula e) l
  | PureFun (x,t,e) -> F.varbind `LAM (var x) (ty t) (formula e) l
  | Let ((tl,rl,el),e1,x,e2,NoRec) -> 
      F.polylet_ (List.map tyvar tl, List.map rvar rl, List.map effvar el)
        (var x) (formula e1) (formula e2) l
  | Let (_,_,_,_,Rec _) -> assert false

(*       of Ty.Generalize.t * ('a,'b,'c) t' * Name.t * ('a,'b,'c) t' * isrec *)
  | Axiom _ | Logic _ | Annot _ | TypeDef _ -> assert false
(*       Format.printf "broke: %a@." print e; assert false *)
  | Param _ | For _ | LetReg _ -> assert false
(*   | Ite of ('a,'b,'c) t' * ('a,'b,'c) t' * ('a,'b,'c) t' *)
  | _ -> assert false
and wp m q e = 
  let ft = ty e.t and eff = effect e.e and l = e.loc in
  if is_value_node e then
    F.and_ (F.applist [q;m;lift_value e] l) (correct e) l
  else 
    match e.v with
    | LetReg (rl,e) -> 
        let rl = List.map rvar rl in
        let ef = List.fold_right Effect.radd rl Effect.empty in 
        F.rgen rl 
        (F.effFAho ef (fun cur ->
          wp_node (F.combine m cur l)
            (F.efflamho (Effect.union eff ef) (fun s -> 
              F.app q (F.restrict eff s l) l) l) e) l) l
    | App (v1,v2,_,_) -> 
        let lv1 = lift_value v1 and lv2 = lift_value v2 in
(*
        Format.printf "app: %a; %a : %a@." print e F.print lv1 Fty.print
        (F.get_type lv1);
*)
        F.andlist 
        [ correct v1; correct v2;
          F.applist [F.pre lv1 l; lv2; m ] l;
          F.effFAho eff (fun m2 -> 
            F.forallho ft (fun x ->
              F.impl (F.applist [F.post lv1 l; lv2; m; m2; x] l)
                (F.applist [q;m2; x] l) l) l) l ] l 
    | Let (g,e1,x,e2,_) -> 
        let x = var x in
        let g = gen g in
        if is_value_node e1 then
          let lv = lift_value e1 in
          let f = F.gen g (correct e1) l in
          F.and_ f (F.polylet_ g x lv (wp_node m q e2) l) l
        else
          let t = ty e1.t in
          let f = F.efflamho (effect e1.e) (fun m2 ->
            F.lam x t (wp_node (F.combine m m2 l) q e2) l) l in
          wp_node m f e1
    | Ite (c,th,el) ->
        let lc = lift_value c in
        let branch boolean e = F.impl (F.eq lc (boolean l) l) (wp_node m q e) l in
        F.and_ (branch F.btrue th) (branch F.bfalse el) l
    | _ -> assert false
and wp_node m q e = wp m q e

let rec decl e = 
  let l = e.loc in
  match e.v with
  | Let (g,e1,x,e2,_) ->
(*       Format.printf "%a@." Name.print x; *)
      let g' = gen g and x' = var x and s = Name.to_string x in
      if is_param e1 then `Param (x', g', (ty e1.t), lift_value e1) :: decl e2
      else
        begin match e1.v with
        | Axiom e -> `Axiom (s, formula e) :: decl e2
        | Logic t -> `Logic (x', gen_restrict g, ty t) :: decl e2
        | Param _ -> assert false
        | _ -> 
            let eff = effect e1.e in
            let t = ty e1.t in
            let q = F.efflamho eff (fun _ -> F.lamho t (fun _ -> F.true_ l) l) l in
            let refl = lift_value e1 in
            `Goal (s, F.gen g' (F.effFAho eff (fun m -> wp_node m q e1) l) l)
              :: `Param (x',g',t,refl) :: decl e2
        end
  | TypeDef ((tl,_,_),_,x,e) -> `Type (List.length tl, tyvar x) :: decl e
  | Const _ -> []
  | _ -> assert false


let main e = decl e
      
(*

and wp_node m q e = 
  let t = e.t and _ = e.e and l = e.loc in
  if is_value_node e then
    and_ (applist [q;m;lift_value e] l) (correct e) l
  else
    match e.v with
    | Const _ | Name _ | Lam _ | PureFun _ | For _ | Annot _ -> 
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
