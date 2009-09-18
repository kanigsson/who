open Ast
open Recon
module G = Ty.Generalize

exception Error of string * Loc.loc
let error s loc = raise (Error (s,loc))

let ty = Ty.to_logic_type

let rec lift_value v = 
(*   Format.printf "lift: %a@." print v ; *)
  let l = v.loc in
  match v.v with
  | Var _ -> { v with t = ty v.t }
  | Const _ | Logic _ | Axiom _ | Quant _ -> v
  | App (v1,v2,kind,_) -> 
(*       Format.printf "app: %a,%a@." print v1 print v2; *)
      app ~kind (lift_value v1) (lift_value v2) l
  | PureFun (t,(_,x,e)) -> 
      plam x (ty t) (lift_value e) l
  | Lam (x,t,p,e,q) ->
      let t = ty t and eff = NEffect.clean e.e in
      let _,p = p and _,_,q = q in
      let p = 
        match p with 
        | None -> plam x t (efflamho eff (fun _ -> ptrue_ l) l) l
        | Some p -> plam x t p l 
      and q = 
        match q with
        | PResult _ -> assert false
        | PNone ->
            plam x t (
              efflamho eff (fun _ -> 
                efflamho eff (fun _ -> 
                  plamho (ty e.t) (fun _ -> ptrue_ l) l) l) l) l
        | PPlain q -> plam x t q l in
      mk_tuple p q l
  | _ -> 
      error (Myformat.sprintf "not a value: %a" print v) l

let rec correct v = 
(*   Format.printf "correct: %a@." print v ; *)
  let l = v.loc in
  match v.v with
  | Var _ | Const _ | Axiom _ | Logic _ | Quant _ -> ptrue_ l
  | App (v1,v2,_,_) -> and_ (correct v1) (correct v2) l
  | Lam (x,t,p,e,q) -> 
      let lt = ty t and eff = NEffect.clean e.e in
      effFA eff (fun r ->
        let p = match p with 
                | _,None -> ptrue_ l
                | _,Some f -> app f r l in
        let q = match q with 
                | _,_,PNone -> 
                    efflamho eff (fun _ ->
                      plamho (ty e.t) (fun _ -> ptrue_ l) l) l
                | _,_,PResult _ -> assert false
                | _,_,PPlain f -> app f r l in
        sforall x lt (impl p (wp_node r q e) l) l) l
  | PureFun (t,(_,x,e)) -> sforall x (ty t) (correct e) l
  | _ -> 
      Myformat.printf "correct: not a value: %a@." print v;
      assert false
and wp m q e = 
  let ft = ty e.t and l = e.loc in
  if is_value_node e then
    and_ (applist [q;m;lift_value e] l) (correct e) l
  else 
    match e.v with
    | LetReg (rl,se) -> 
        let ef = List.fold_right NEffect.radd rl NEffect.empty in 
        let eff = NEffect.clean se.e in
        let resteff = NEffect.clean e.e in
        rgen rl 
        (effFA ef (fun cur ->
          wp_node (combine m cur l)
            (efflamho (NEffect.union eff ef) (fun s -> 
              app q (restrict resteff s l) l) l) se) l) l
    | App (v1,v2,_,_) -> 
        let lv1 = lift_value v1 and lv2 = lift_value v2 
        and eff = NEffect.clean e.e in
(*         Format.printf "app; v1 of type %a; effect : %a@." *)
(*         Ty.print v1.t NEffect.print eff; *)
(*         Format.printf "app: %a; %a : %a@." print e print lv1 Ty.print lv1.t;
 *         *)
        andlist 
        [ correct v1; correct v2;
          applist [pre lv1 l; lv2; m ] l;
          effFA eff (fun m2 -> 
            forall ft (fun x ->
              impl (applist [post lv1 l; lv2; m; m2; x] l)
                (applist [q;m2; x] l) l) l) l ] l 
    | Let (p,g,e1,b,r) -> 
        let x,e2 = sopen b in
        (* TODO recursive case *)
        if is_value_node e1 then
          let lv = lift_value e1 in
          let f = gen g (correct e1) l in
          let wp = wp_node m q e2 in
          let gen f = let_ ~prelude:p g lv x f NoRec l in
          match r with
          | NoRec -> and_ f (gen wp) l
          | Rec _ -> gen (and_ f wp l)

        else
          let t = ty e1.t in
          let eff = e.e in
          let f = efflamho eff (fun m2 ->
            plam x t (wp_node (combine m m2 l) q e2) l) l in
          wp_node m f e1
    | Ite (c,th,el) ->
        ite (eq (lift_value c) (btrue_ l) l) 
          (wp_node m q th) (wp_node m q el) l
(*
        let lc = lift_value c in
        let branch boolean e = impl (eq lc (boolean l) l) (wp_node m q e) l in
        and_ (branch btrue_ th) (branch bfalse_ el) l
*)
    | Param _ -> ptrue_ l
    | TypeDef (g,k,x,e) -> typedef g k x (wp_node m q e) l
    | _ -> assert false
and wp_node m q e = 
  if NEffect.sequal (domain m) e.e then wp m q e
  else begin
(*     Format.printf "q: %a; effects: %a <= %a@."  *)
(*       print q NEffect.print e.e NEffect.print (domain m); *)
    let l = e.loc in
    wp (restrict e.e m l) 
      (efflamho e.e (fun m2 -> app q (combine m m2 l) l) l) 
      e
  end

let main e = 
  let l = e.loc in
  let eff = NEffect.clean e.e in
  let q = efflamho eff  (fun _ -> plamho e.t (fun _ -> ptrue_ l) l) l in
    effFA eff (fun m -> (wp_node m q e)) l
