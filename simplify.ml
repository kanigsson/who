open Name
open Const
open Ast
open Recon

module NPair = struct
  type t = Name.t * Name.t
  let compare = Misc.pair_compare Name.compare Name.compare
end

module NPM = Map.Make(NPair)

exception No_Match

type env = 
  { rtypes : Ty.t Name.M.t ; 
    renames : Name.t NPM.t;
    et : Ty.t;
    l : Loc.loc
  }
let empty = 
  { rtypes = Name.M.empty ; renames = NPM.empty; et = Ty.unit; l = Loc.dummy }


let rtype_add n t env = 
  { env with rtypes = Name.M.add n t env.rtypes }
let rtype n env = 
  try Name.M.find n env.rtypes
  with Not_found -> 
    failwith 
    (Myformat.sprintf "type not found for region: %a@." 
      Name.print n)

let rec find_type rname x =
(*   Myformat.printf "find_type: %a in %a@." Name.print rname print x; *)
  match Ty.find_type_of_r rname x.t with
  | Some x -> x
  | None -> 
      match x.v with
      | Quant (_,t,b) ->
          begin match Ty.find_type_of_r rname t with
          | Some x -> x
          | None -> 
              let _,e = sopen b in
              find_type rname e
          end
      | _ -> assert false


let name_add n1 n2 n3 env =
  Myformat.printf "adding (%a,%a) -> %a@." Name.print n1 Name.print n2 Name.print
  n3;
  { env with renames = NPM.add (n1,n2) n3 env.renames;
(*
    rtypes = 
      try Name.M.add n3 (rtype n1 env) env.rtypes 
      with Not_found -> env.rtypes  
*)
  }

let getname n1 n2 env = 
  try NPM.find (n1,n2) env.renames 
  with Not_found -> 
    failwith 
    (Myformat.sprintf "name not found in state: %a, %a@." 
      Name.print n1 Name.print n2)

let build_var r v env = 
  let nv = getname r v env in
(*
  Myformat.printf "from (%a, %a), building: %a@." 
    Name.print r Name.print v Name.print nv;
*)
  svar nv (rtype r env) env.l

type simpl = 
  | Nochange
  | Simple_change of Recon.t
  | Change_rerun of Recon.t

let logic_simpl _ l t x =
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

let unit_void _ l t = function
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

let boolean_prop _ l _ x = 
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

let tuple_reduce _ _ _ = function
  | App ({ v = Var ({name=Some ("fst" | "pre" | "snd" | "post" as n) },_)},t,_,_) 
  ->
      begin match destruct_app2_var t with
      | Some ({name = Some "," },_,a,b) ->
          if n = "fst" || n = "pre" then Simple_change a else Simple_change b
      | _ -> Nochange
      end
  | _ -> Nochange

let elim_eq_intro _ _ _ = function
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

let quant_over_true _ l _ x =
  let s = Simple_change (ptrue_ l) in
  match x with
  (* we can directly access the value here, because constants are not subject to
   * substitutions *)
  | Quant (_,_,(_,_,{v = Const Ptrue})) -> s
  | Gen (_,{v = Const Ptrue}) -> s
  | Let (_,_,_,(_,_,{v = Const Ptrue}), _) -> s
  | EndSec {v = Const Ptrue} -> s
  | Section (_,_,{ v = Const Ptrue }) -> s
  | TypeDef (_,_,_,{v = Const Ptrue}) -> s
  | _ -> Nochange

let beta_reduce _ _ _ = function
  | App ({v = PureFun (_, l)} ,f2,_,_) ->
      let x,body = vopen l in
      Change_rerun (subst x (fun _ -> f2.v) body)
  | Let (_,_,{v = Axiom _ | Logic _ },_,_) ->
      Nochange
  | Let (_,g,v,l,_) -> 
      let x,e = vopen l in
(*       Myformat.printf "substing ∀[%a].%a in %a@." Ty.Generalize.print g
 *       Name.print x print e; *)
      Change_rerun (polsubst g x v e)
  | _ -> Nochange

let get_restrict_combine _ l _ x = 
  match destruct_get' x with
  | Some (_,r,_,map) -> 
      begin match destruct_restrict map with
      | Some (map,_,_) -> Simple_change (get r map l)
      | None -> 
          begin match destruct_combine map with
          | Some (m1,_,m2,e2) -> 
              let f = 
                if NEffect.rmem (Ty.get_reg r.t) e2 then get r m2 l 
                else get r m1 l in
              Simple_change f
          | None -> Nochange
          end
      end
  | _ -> Nochange

let get_map env _ _ x = 
  match destruct_get' x with
  | Some (_,r,_,{v = Var (v,_)}) -> 
      let nf = build_var (Ty.get_reg r.t) v env in
(*
      Myformat.printf "found get(%a,%a), building %a@." print r Name.print v
      print nf;
*)
      Simple_change nf
  | _ -> Nochange

type effrec = Name.t Name.M.t * Name.t Name.M.t

let e_combine (r1,e1) (r2,e2) = 
  Name.M.fold Name.M.add r2 r1,
  Name.M.fold Name.M.add e2 e1

let e_restrict d (r,e) = 
  Name.M.fold (fun k v acc -> 
    if NEffect.rmem k d then Name.M.add k v acc else acc) r Name.M.empty,
  Name.M.fold (fun k v acc -> 
    if NEffect.emem k d then Name.M.add k v acc else acc) e Name.M.empty

let rec form2effrec t x = 
  match destruct_combine' x with
  | Some (m1,_,m2,_) -> e_combine (form2effrec m1.t m1.v) (form2effrec m2.t m2.v)
  | None -> 
      match destruct_restrict' x with
      | Some (m,_,e2) -> e_restrict e2 (form2effrec m.t m.v)
      | None ->
          match x with
          | Var (s,_) -> 
              let d = Ty.domain t in
              NEffect.rfold (fun k acc -> Name.M.add k s acc) Name.M.empty d,
              NEffect.efold (fun k acc -> Name.M.add k s acc) Name.M.empty d 
          | _ -> 
              Myformat.printf "strange term: %a@." print' x;
              assert false

let effref2form env (r,_) =
  (* TODO effect vars *)
  Name.M.fold (fun r s acc ->
    app 
      (app2 (pre_defvar "kset" ([rtype r env],[],[]) env.l)
      (svar r (Ty.spredef_var "key") env.l) 
      (build_var r s env) env.l) 
      acc env.l) r (spre_defvar "kempty" env.l )



let replace_map env _ t x =
  if Ty.is_map t then
    let m = form2effrec t x in
    let f = effref2form env m in
    Simple_change f
  else Nochange

let simplifiers =
  [
    beta_reduce;
    logic_simpl;
    tuple_reduce;
    elim_eq_intro;
    unit_void;
    quant_over_true;
    boolean_prop;
    get_restrict_combine
  ]

let simplify_maps = 
  [ 
    get_map; 
    replace_map;
  ]

let exhaust simplifiers env f = 
  let rec aux b f = function
    | [] when b -> Simple_change f
    | [] -> Nochange
    | simpl :: xs ->
        match simpl env f.loc f.t f.v with
        | Change_rerun f -> Change_rerun f
        | Simple_change f -> aux true f simplifiers
        | Nochange -> aux b f xs in
  aux false f simplifiers

let add_effect env x d = 
  let env,rl = 
    NEffect.rfold (fun r (env,rl) -> 
      let n = Name.new_name r in
      name_add r x n env, (n,rtype r env)::rl) (env,[]) d in
  let env, el = 
    NEffect.efold (fun e (env,el) -> 
      let n = Name.new_name e in
      name_add e x n env, n::el) (env,[]) d in
  env, rl,el

let simplify ~genbind ~(varbind : 'a -> [`FA | `LAM | `EX] -> 'b) simplifiers f = 
(*   Format.printf "simplify: %a@." print f; *)
  let rec simplify env f = 
    let l = f.loc in
    let env = { env with l = f.loc; et = f.t } in
    let f = 
      match f.v with
      | (Const _  | Var _ | Logic _ | Axiom _ ) -> f
      | App (f1,f2,k,c) -> 
          app ~kind:k ~cap:c (simplify env f1) (simplify env f2) l
      | Gen (g,t) -> 
          let env = genbind g env t in
          gen g (simplify env t) l
      | Let (p, g ,e1,b,r) ->
          let x,e2 = if p then sopen b else vopen b in
          let env' = genbind g env e1 in
          let_ ~prelude:p g (simplify env' e1) x (simplify env e2) r l
      | PureFun (t,b) ->
          let x,e = vopen b in
          varbind env `LAM x t (fun env -> simplify env e) l
      | Quant (k,t,b) -> 
          let x,e = vopen b in
          varbind env (k :> [`EX | `FA | `LAM ]) x t (fun env -> simplify env e) l
      | Ite (e1,e2,e3) -> 
          ite (simplify env e1) (simplify env e2) (simplify env e3) l
      | TypeDef (g,t,x,e) -> 
          typedef g t x (simplify env e) l
      | Section (n,f,e) -> 
          section n f (simplify env e) l
      | EndSec e -> endsec (simplify env e) l 
      | Lam _ | Annot _ | Param _ | For _ | LetReg _ -> assert false in
    match exhaust simplifiers env f with
    | Nochange -> f
    | Simple_change f -> f
    | Change_rerun f -> simplify env f
  in
  simplify empty f

let allsimplify f =
  let f = simplify (fun _ env _ -> env) 
                   (fun env k x t e l -> aquant k x t (e env) l) simplifiers f in
  Myformat.printf "=============@.%a@.=================@." print f;
  let f = 
    simplify 
      (fun (_,rl,_) env t -> 
        List.fold_left (fun env r -> rtype_add r (find_type r t) env) env rl)
      (fun env k x t e l ->
        if Ty.is_map t then
          let env, rl,el = add_effect env x (Ty.domain t) in
          let e = e env in
          let f = List.fold_left (fun acc (x,t) -> aquant k x t acc l) e rl in
          List.fold_left (fun acc e -> 
            aquant k e (Ty.spredef_var "kmap") acc l) f el
        else aquant k x t (e env) l)
        simplify_maps f 
  in
  Myformat.printf "<<<<<<<<<<<<<@.%a@.<<<<<<<<<<<<<<<<<@." print f;
  f
