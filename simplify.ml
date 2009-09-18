open Name
open Const
open Ast
open Recon

exception No_Match

type simpl = 
  | Nochange
  | Simple_change of Recon.t
  | Change_rerun of Recon.t

let logic_simpl l t x =
  if t = Ty.prop then
    match x with
    | App ({v = Var ({name = Some "~"},_)},t,_,_) ->
        begin match t.v with
        | Const Ptrue -> Simple_change (pfalse_ l)
        | Const Pfalse -> Simple_change (ptrue_ l)
        | _ -> Nochange
        end
    | Ite ({v = Const Ptrue}, th, _) -> Simple_change th
    | Ite ({v = Const Pfalse}, _, el) -> Simple_change el
    | Ite (_, a, b) when equal a b -> Simple_change a
    | Ite (test,th,el) -> 
        Simple_change (and_ (impl test th l) (impl (neg test l) el l) l)
    | x ->
        match destruct_app2_var' x with
        | Some ({name = Some "/\\" },_, t1, t2) ->
            begin match t1.v, t2.v with
            | Const Ptrue, _ -> Simple_change t2
            | _, Const Ptrue -> Simple_change t1
            | Const Pfalse, _ | _, Const Pfalse -> Simple_change (pfalse_ l)
            | _, _ -> Nochange end
        | Some ({name = Some "->" },_, t1, t2) ->
            begin match t1.v, t2.v with
            | Const Ptrue, _ -> Simple_change t2
            | Const Pfalse, _ | _, Const Ptrue -> Simple_change (ptrue_ l)
            | t1,t2 when equal' t1 t2 -> Simple_change (ptrue_ l)
            | t1,_ ->
                begin match destruct_app2_var' t1 with
                | Some ({name = Some "/\\"},_,h1,h2) ->
                    Simple_change (impl h1 (impl h2 t2 l) l)
                | _ -> Nochange end end
        | Some ({name = Some "=" },_, t1, t2) when equal t1 t2 ->
            Simple_change (ptrue_ l)
        | _ -> Nochange 
  else Nochange

let unit_void l t = function
  | Var _ when Ty.equal t Ty.unit -> Simple_change (void l)
  | Var ({name = Some "empty"},_) -> Nochange
  | Var _ ->
      begin match t with
      | Ty.C (Ty.Map e) when NEffect.is_empty e -> Simple_change (mempty l)
      | _ -> Nochange
      end
  | Quant (_, Ty.C (Ty.Const TUnit),b) -> 
      let _,f = vopen b in Simple_change f
  | Quant (_, Ty.C (Ty.Map e),b) when NEffect.is_empty e -> 
      let _,f = vopen b in Simple_change f
  | _ -> Nochange

let boolean_prop l _ x = 
  try match destruct_app2_var' x with
  | Some ({name = Some "="},_,t1,{v = (Const Btrue | Const Bfalse as n)}) ->
      begin match destruct_app2_var t1 with
       | Some (op, _,arg1, arg2) ->
           let op = 
             match op with 
             | {name = Some "<<=" } -> "<="
             | {name = Some "<<" } -> "<"
             | {name = Some ">>" } -> ">"
             | {name = Some ">>=" } -> ">>="
             | {name = Some "==" } -> "=="
             | {name = Some "!=" } -> "!="
             | _ -> raise No_Match in
           let f = appi (spre_defvar op l) arg1 arg2 l in
           if n = Const Btrue then Simple_change f 
           else Simple_change (neg f l)
       | _ -> Nochange
       end
  | _ -> Nochange
  with No_Match -> Nochange

let tuple_reduce _ _ = function
  | App ({ v = Var ({name=Some ("fst" | "pre" | "snd" | "post" as n) },_)},t,_,_) 
  ->
      begin match destruct_app2_var t with
      | Some ({name = Some "," },_,a,b) ->
          if n = "fst" || n = "pre" then Simple_change a else Simple_change b
      | _ -> Nochange
      end
  | _ -> Nochange

let elim_eq_intro _ _ = function
  | Quant (`FA,_,b) ->
      let x,f = vopen b in
      begin match destruct_app2_var f with
      | Some ({name = Some "->"}, _, t1,f)  ->
          begin match destruct_app2_var t1 with
          | Some ({name= Some "="}, _,{v= Var(y,_)}, def) when Name.equal x y ->
              Change_rerun (subst x (fun _ -> def.v) f)
          | Some ({name= Some "=" }, _,def,{v = Var (y,_)}) when Name.equal x y ->
              Change_rerun (subst x (fun _ -> def.v) f)
          | _ -> Nochange
          end
(*
      | Some ({name = Some "/\\" }, t1,t2) ->
          begin match destruct_infix t1, destruct_infix t2 with
          | Some ({name=Some "->"},eq1, f1), Some ({name=Some "->"},eq2,f2) ->
              begin match destruct_infix eq1, destruct_infix eq2 with
              | Some ({name = Some "="}, {v = Var (x1,_)}, def1), 
                Some ({name = Some "="}, {v = Var (x2,_)}, def2) when
                  Name.equal x1 x && Name.equal x2 x ->
                    Change_rerun (and_ 
                    (subst x1 (fun _ -> def1.v) f1)
                    (subst x2 (fun _ -> def2.v) f2) l)
              | _ -> Nochange
              end
          | _ -> Nochange
          end
*)
      | _ -> Nochange
      end
  | _ -> Nochange

let quant_over_true l _ x =
  let s = Simple_change (ptrue_ l) in
  match x with
  (* we can directly access the value here, because constants are not subject to
   * substitutions *)
  | Quant (_,_,(_,_,{v = Const Ptrue})) -> s
  | Gen (_,{v = Const Ptrue}) -> s
  | Let (_,_,_,(_,_,{v = Const Ptrue}), _) -> s
  | TypeDef (_,_,_,{v = Const Ptrue}) -> s
  | _ -> Nochange

let beta_reduce _ _ = function
  | App ({v = PureFun (_, l)} ,f2,_,_) ->
      let x,body = vopen l in
      Change_rerun (subst x (fun _ -> f2.v) body)
  | Let (_,_,{v = Axiom _ | Logic _ },_,_) ->
      Nochange
  | Let (_,g,v,l,_) -> 
      let x,e = vopen l in
      Change_rerun (polsubst g x v e)
  | _ -> Nochange

let get_map l _ x = 
  match destruct_get' x with
  | Some (_,r,_,map) -> 
      begin match destruct_restrict map with
      | Some (map,_,_) -> Simple_change (get r map l)
      | None -> 
          begin match destruct_combine map with
          | Some (m1,_,m2,e2) -> 
              let reg = match r.t with | Ty.C (Ty.Ref (reg,_)) -> reg 
                                       | _ -> assert false in
              let f = if NEffect.rmem reg e2 then get r m2 l else get r m1 l in
              Simple_change f
          | None -> Nochange
          end
      end
  | _ -> Nochange

let simplifiers =
  [
    beta_reduce;
    logic_simpl;
    tuple_reduce;
    elim_eq_intro;
    unit_void;
    quant_over_true;
    boolean_prop;
    get_map;
  ]

let exhaust f = 
  let rec aux b f = function
    | [] when b -> Simple_change f
    | [] -> Nochange
    | simpl :: xs ->
        match simpl f.loc f.t f.v with
        | Change_rerun f -> Change_rerun f
        | Simple_change f -> aux true f simplifiers
        | Nochange -> aux b f xs in
  aux false f simplifiers

let rec simplify f = 
(*   Format.printf "simplify: %a@." print f; *)
  let f = 
    { f with v = 
    match f.v with
    | (Const _  | Var _ | Logic _ | Axiom _ ) -> f.v
    | App (f1,f2,k,c) -> App (simplify f1, simplify f2, k, c)
    | Gen (g,t) -> Gen (g, simplify t)
    | Let (p, g,e1,b,r) ->
        let x,e2 = if p then sopen b else vopen b in
        Let (p, g, simplify e1, close x (simplify e2),r)
    | PureFun (t,b) ->
        let x,e = vopen b in
        PureFun (t, close x (simplify e))
    | Quant (k,t,b) -> 
        let x,e = vopen b in
        Quant (k,t, close x (simplify e))
    | Ite (e1,e2,e3) -> Ite (simplify e1, simplify e2, simplify e3)
    | TypeDef (g,t,x,e) -> TypeDef (g,t,x,simplify e) 
    | Lam _ | Annot _ | Param _ | For _ | LetReg _ -> assert false } in
  match exhaust f with
  | Nochange -> f
  | Simple_change f -> f
  | Change_rerun f -> simplify f

