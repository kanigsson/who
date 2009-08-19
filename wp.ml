open Vars
open Ast
open Recon

module M = Myformat

exception Error of string * Loc.loc
let error s loc = raise (Error (s,loc))

let rec lift_value v = 
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
        | None -> plam x t (efflam_ho e.e (fun m -> ptrue_ l) l) l
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

let rec correct v = 
  M.printf "correct@.";
  let l = v.loc in
  match v.v with
  | Var _ | Const _ | Axiom _ | Logic _  -> ptrue_ l
  | App (v1,v2,_,_) -> 
      (* suppose that the application is pure *)
      and_ (correct v1) (correct v2) l
  | For _ | Annot _ | Let _ | Ite _ | TypeDef _ | Quant _
  | Param _ | LetReg _ -> assert false
  | PureFun (x,t,e) -> sforall x (Ty.to_logic_type t) e l
  | Lam (x,t,p,e,q) -> 
      let _,p = p and _,_,q = q in
      match q with
      | PNone -> ptrue_ l
      | PResult _ -> assert false
      | PPlain q ->
          let lt = Ty.to_logic_type t in
          effFA e.e (fun r ->
            let p = 
              match p with 
              | None -> ptrue_ l 
              | Some f -> app f r l in
            sforall x lt
              (impl p
                (wp_node r (app q r l) e) l) l) l

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
    | Param (t,e) -> ptrue_ l
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
