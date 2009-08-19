open Vars
open Ast
open Recon

let rec correct v = 
  let l = v.loc in
  match v.v with
  | Var _ | Const _ | Axiom _ | Logic _  -> ptrue_ l
  | App (v1,v2,_,_) -> 
      (* suppose that the application is pure *)
      and_ (correct v1) (correct v2) l
  | For _ | Annot _ | Let _ | Ite _ | TypeDef _ | Quant _
  | Param _ | LetReg _ -> assert false
  | PureFun (x,t,e) -> forall x (Ty.to_logic_type t) e l
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
  let t = e.t and eff = e.e and l = e.loc in
  if is_value_node e then
    and_ (applist [q;m;lift_value v] l) (correct v) l
  else
    match e.v with
    | Const _ | Var _ | Lam _ | PureFun _ | For _ | Annot _ -> 
        assert false
    | Axiom t -> axiom t loc
    | Logic t -> logic t loc
    | App of ('a,'b,'c) t' * ('a,'b,'c) t' * Const.fix * RVar.t list
    | Let of Ty.Generalize.t * ('a,'b,'c) t' * Var.t * ('a,'b,'c) t' * isrec
    | Ite of ('a,'b,'c) t' * ('a,'b,'c) t' * ('a,'b,'c) t'
    | TypeDef of Ty.Generalize.t * Ty.t option * TyVar.t * ('a,'b,'c) t'
    | Quant of Const.quant * Var.t * Ty.t * ('a,'b,'c) t'
    | Param of Ty.t * Effect.t
    | LetReg of RVar.t list * ('a,'b,'c) t'
    
