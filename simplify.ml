open Name
open Const
open Ast
open Recon
module PL = Predefined.Logic

module NPair = struct
  type t = Name.t * Name.t
  let compare = Misc.pair_compare Name.compare Name.compare
end

module NPM = Map.Make(NPair)

(* rtypes : returns a type for a region name 
   renames : retuns a unique name for a couple (region, state) 
   et : current type 
   l : current location
*)
type env = 
  { rtypes : Ty.t Name.M.t ; 
    renames : Name.t NPM.t;
    et : Ty.t;
    l : Loc.loc
  }

let empty = 
  { rtypes = Name.M.empty ; renames = NPM.empty; et = Ty.unit; l = Loc.dummy }


  (* [rtype_add] adds a type for a given region name *)
let rtype_add n t env = 
  { env with rtypes = Name.M.add n t env.rtypes }

  (* [rtype] finds the type for a region name *)
let rtype env n = 
  try Name.M.find n env.rtypes
  with Not_found -> 
    failwith 
    (Myformat.sprintf "type not found for region: %a@." 
      Name.print n)

(* [find_type] searches for a [tau ref(r)] in the given term *)
let find_type rname x =
(*   Myformat.printf "find_type: %a in %a@." Name.print rname print x; *)
  let rec aux x =
    match Ty.find_type_of_r rname x.t with
    | Some x -> x
    | None -> 
        match x.v with
        | Quant (_,t,b)
        | PureFun (t,b) ->
            begin match Ty.find_type_of_r rname t with
            | Some x -> x
            | None -> 
                let _,e = sopen b in
                aux e
            end
        | Gen (_,t) -> aux t
        | App (t1,t2,_,_) -> 
            begin try aux t1 
            with _ -> aux t2 end
        | _ -> assert false in
  try aux x with e ->
    Myformat.printf "finding no type for %a in %a@." Name.print rname print x;
    raise e

(* add the mapping (n1,n2) -> n3 to the environment for names
 * n1: region
 * n2: state
 * n3: fresh name
 * *)

let name_add n1 n2 n3 env =
  { env with renames = NPM.add (n1,n2) n3 env.renames; }

(* find the name corresponding to (n1,n2) *)
let getname n1 n2 env = 
  try NPM.find (n1,n2) env.renames 
  with Not_found -> 
    failwith 
    (Myformat.sprintf "name not found in state: %a, %a@." 
      Name.print n1 Name.print n2)

(* for region [r] and state [v], build the term variable using the fresh name
 * corresponding to (r,v) *)
let build_var r v env = 
  let nv = getname r v env in
  svar nv (rtype env r) env.l

(* for effect var [e] and state [v], build the term variable using the fresh name
 * corresponding to (r,v) - an effect variable is its own type *)
let build_evar e v env = 
  let nv = getname e v env in
  svar nv (Ty.var e) env.l

(* a simplification either does nothing, a simple top-level change, or a deeper
 *  change requiring all simplifications to rerun *)
type simpl = 
  | Nochange
  | Simple_change of Recon.t
  | Change_rerun of Recon.t

(* transform f (m : <r1 r2| e>) into f r1m r2m em *)
let distrib_app env x =
  let l = env.l in
  match x with
  | App (t1,t2,_,_) when Ty.is_map t2.t -> 
      let er = Effrec.from_form_t t2.t t2.v in
      let t1 = {t1 with t = Ty.selim_map (rtype env) t1.t} in
      let f = Effrec.rfold (fun r s acc -> 
        app acc (build_var r s env) l) er t1 in
      let f = Effrec.efold (fun e s acc -> 
        app acc (build_evar e s env) l) er f in
      Simple_change f
  | _ -> Nochange

(* transform !! x m into m_x *)
let get_map env x = 
(*   Myformat.printf "get_form: %a@." print' x; *)
  match destruct_get' x with
  | Some (_,_,reg,dom,m) -> 
      let (rm,_) = Effrec.from_form dom m.v in
      let nf = build_var reg (Name.M.find reg rm) env in
      Simple_change nf
  | _ -> 
(*       Myformat.printf "get_form: %a@." print' x; *)
      Nochange

let simplify_maps = 
  [ 
    get_map; 
    distrib_app;
  ]

let exhaust simplifiers env f = 
  let rec aux b f = function
    | [] when b -> Simple_change f
    | [] -> Nochange
    | simpl :: xs ->
        match simpl env f.v with
        | Change_rerun f -> Change_rerun f
        | Simple_change f -> aux true f simplifiers
        | Nochange -> aux b f xs in
  aux false f simplifiers

let add_effect env x d = 
(*   Myformat.printf "adding effect : %a@." NEffect.print d; *)
  let env,rl = 
    NEffect.rfold (fun r (env,rl) -> 
      let n = Name.new_name r in
      name_add r x n env, (n,rtype env r)::rl) (env,[]) d in
  let env, el = 
    NEffect.efold (fun e (env,el) -> 
      let n = Name.new_name e in
      name_add e x n env, (e,n)::el) (env,[]) d in
  env, rl,el

let simplify ~genbind 
             ~(varbind : 'a -> [`FA | `LAM | `EX] -> 'b) 
             ~tyfun before after env f = 
  let rec aux env f = 
    let l = f.loc in
    let env = { env with l = f.loc; et = f.t } in
    let f =
      match exhaust before env f with
      | Nochange -> f
      | Simple_change f -> f
      | Change_rerun f -> aux env f in
    let f = 
      match f.v with
      | (Const _ ) -> f
      | Var (v,i) -> 
          Myformat.printf "treating var: %a@." Name.print v;
          var_i v (Inst.map (tyfun env) Misc.id Misc.id i) (tyfun env f.t) l
      | App (f1,f2,k,c) -> 
          app ~kind:k ~cap:c (aux env f1) (aux env f2) l
      | Gen (g,t) -> 
          let g,t = genbind g env t in
          gen g t env.l
      | Let (g ,e1,b,r) ->
          let x,e2 = vopen b in
          let g,e1 = genbind g env e1 in
          let_ g e1 x (aux env e2) r l
      | PureFun (t,b) ->
          let x,e = vopen b in
          varbind env `LAM x t e l
      | Quant (k,t,b) -> 
          let x,e = vopen b in
          varbind env (k :> [`EX | `FA | `LAM ]) x t e l
      | Ite (e1,e2,e3) -> 
          ite (aux env e1) (aux env e2) (aux env e3) l
      | Lam _ | Annot _ | For _ | LetReg _ | Param _ -> assert false in
    let f =
      match exhaust after env f with
      | Nochange -> f
      | Simple_change f -> f
      | Change_rerun f -> aux env f in
    let f = {f with t = tyfun env f.t} in
    f
  in
  aux env f

let tyfun env t = Ty.selim_map (rtype env) t

let map_simplify f = 
  let rec genbind (tvl,rl,el) env t = 
    let env = List.fold_left (fun env r -> 
      rtype_add r (find_type r t) env) env rl in
    let env = List.fold_left (fun env e ->
      rtype_add e (Ty.var e) env) env el in
    let t = aux env t in
    (* effect variables become type variables *)
    (tvl@el,[],[]), t

  and varbind env k x t e l =
    if Ty.is_map t then
      let env, rl, el = add_effect env x (Ty.domain t) in
      let e = aux env e in
      let f = List.fold_left (fun acc (x,t) -> aquant k x t acc l) e rl in
      List.fold_left (fun acc (old,new_) -> 
        aquant k new_ (rtype env old) acc l) f el
    else if Ty.is_ref t then aux env e
    else aquant k x (Ty.selim_map (rtype env) t) (aux env e) l

  and aux env f =
    simplify ~genbind ~varbind ~tyfun simplify_maps [] env f in
  let rec decl env d = 
    Myformat.printf "%a@." print_decl d;
    match d with
    | Logic (n,_,_) when Name.S.mem n PL.effrec_set -> env, []
    | Logic (s,((_,[],[]) as g),t) -> env, [Logic (s,g,tyfun env t)]
    | DLetReg _ -> 
        (* TODO *)
        env, [d]
    | TypeDef _ -> env, [d]
    | Formula (n,f,k) -> env, [Formula (n, aux env f, k)]
    | Section (s,cl,th) -> 
        let env, th = theory env th in
        env, [Section (s,cl,th)]
    | Program (n,g,t,LogicDef) -> 
        let g,t = genbind g env t in
        env, [Program (n,g,t,LogicDef)]
    | Program _ | Logic _ -> assert false 
  and theory env th = 
    let env, l = Misc.list_fold_map decl env th in
    env, List.flatten l in
  let _, th = theory empty f in
  th

let term env t =
  rebuild_map 
    ~varfun:(fun z i def ->
      try 
        let g,t = Name.M.find z env in
        allsubst g i t
      with Not_found -> def)
    ~termfun:(fun t ->
      match t.v with
      | Let (g,e1,b,_) ->
          let x,e2 = vopen b in
          polsubst g x e1 e2
      | Const _ | Var _ | App _ | Gen _ | PureFun _ | Quant _ | Ite _ 
      | Lam _ | Annot _ | For _ | LetReg _ | Param _ -> t)
    t

let rec decl env d = 
  match d with
  | Logic _ | TypeDef _ | DLetReg _ -> env, [d]
  | Formula (n,f,k) -> env, [Formula (n, term env f, k) ]
  | Section (s,cl,th) -> 
      let env, th = theory env th in
      env, [Section (s,cl,th)]
  | Program (n,g,t,LogicDef) -> Name.M.add n (g,term env t) env, []
  | Program _ -> assert false
and theory env th = 
  let env, l = Misc.list_fold_map decl env th in
  env, List.flatten l
(*
  List.fold_left (fun (env, acc) d -> 
    let env, th  = decl env d in
    env, th@acc) (env,[]) th
*)

let inline_let th = 
  let _, th = theory Name.M.empty th in
  th
  
let map = map_simplify
