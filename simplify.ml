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
        | Let (_,_,{ v = Logic t} ,b,_) ->
            begin match Ty.find_type_of_r rname t with
            | Some x -> x
            | None -> let _,e = sopen b in aux e
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

(* transform !! x m into m|x *)
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
(*   Format.printf "simplify: %a@." print f; *)
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
      | (Const _  | Axiom _ ) -> f
      | Logic t -> logic (tyfun env t) l
      | Var (v,i) -> 
          var_i v (Inst.map (tyfun env) Misc.id Misc.id i) (tyfun env f.t) l
      | App (f1,f2,k,c) -> 
          app ~kind:k ~cap:c (aux env f1) (aux env f2) l
      | Gen (g,t) -> 
          let g,t = genbind g env t in
          gen g t env.l
      | Let (p, g ,e1,b,r) ->
          let x,e2 = if p then sopen b else vopen b in
(*           Myformat.printf "let %b: %a@." p Name.print x; *)
          let g,e1 = genbind g env e1 in
          let_ ~prelude:p g e1 x (aux env e2) r l
      | PureFun (t,b) ->
          let x,e = vopen b in
          varbind env `LAM x t e l
      | Quant (k,t,b) -> 
          let x,e = vopen b in
          varbind env (k :> [`EX | `FA | `LAM ]) x t e l
      | Ite (e1,e2,e3) -> 
          ite (aux env e1) (aux env e2) (aux env e3) l
      | TypeDef (g,t,x,e) -> 
          typedef g t x (aux env e) l
      | Section (n,f,e) -> 
          section n f (aux env e) l
      | EndSec e -> endsec (aux env e) l 
      | Lam _ | Annot _ | For _ | LetReg _ | Param _ -> assert false in
    let f =
      match exhaust after env f with
      | Nochange -> f
      | Simple_change f -> f
      | Change_rerun f -> aux env f in
    let f = {f with t = tyfun env f.t} in
    f
(*
  and pre env (n,p) = n, Misc.opt_map (aux env) p
  and post env (a,b,q) = 
    a,b,
    match q with
    | PNone -> PNone
    | PPlain f -> PPlain (aux env f)
    | PResult _ -> assert false in
*)
  in
  aux env f

let map_simplify f = 
  let rec aux env f =
    simplify 
      ~genbind:(fun (tvl,rl,el) env t -> 
(*
        Myformat.printf "treating gen %a for expression %a@." 
          Ty.Generalize.print g print t;
*)
        let env = List.fold_left (fun env r -> 
          rtype_add r (find_type r t) env) env rl in
        let env = List.fold_left (fun env e ->
          rtype_add e (Ty.var e) env) env el in
        let t = aux env t in
        let t = 
          if Ty.equal t.t Ty.prop then 
            List.fold_left (fun acc r -> 
              aquant `FA r (Ty.spredef_var "key") acc env.l) t rl
        else t in
        (* effect variables become type variables *)
        (tvl@el,[],[]), t )
      ~varbind:(fun env k x t e l ->
(*
        Myformat.printf "varbind: %a : %a. %a" Name.print x Ty.print t print
        e;
*)
        if Ty.is_map t then
          let env, rl, el = add_effect env x (Ty.domain t) in
          let e = aux env e in
          let f = List.fold_left (fun acc (x,t) -> aquant k x t acc l) e rl in
          List.fold_left (fun acc (old,new_) -> 
            aquant k new_ (rtype env old) acc l) f el
        else if Ty.is_ref t then aux env e
        else aquant k x (Ty.selim_map (rtype env) t) (aux env e)  l)
      ~tyfun:(fun env t -> Ty.selim_map (rtype env) t) 
      simplify_maps [] env f in
  aux empty f

let logic_simplify f =
  let l = f.loc in
  let rec aux f = match f.v with
  | (Const _  | Logic _ | Var _ ) -> f
  | Axiom e -> axiom (aux e) l
  | App (f1,f2,k,c) -> app ~kind:k ~cap:c (aux f1) (aux f2) l
  | Gen (g,t) -> gen g (aux t) l
  | Let (p,g,e1,b,r) ->
      let x,e2 = if p then sopen b else vopen b in
      let e2 = aux e2 in
      begin match e1.v with
      | Axiom _ | Logic _ -> let_ ~prelude:p g e1 x e2 r l
      | _ -> polsubst g x (aux e1) e2
      end
  | PureFun (t,b) ->
      let x,e = vopen b in
      aquant `LAM x t (aux e) l
  | Quant (k,t,b) -> 
      let x,e = vopen b in
      squant k x t (aux e) l
  | Ite (e1,e2,e3) -> 
      ite (aux e1) (aux e2) (aux e3) l
  | TypeDef (g,t,x,e) -> typedef g t x (aux e) l
  | Section (n,f,e) -> section n f (aux e) l
  | EndSec e -> endsec (aux e) l 
  | Lam _ | Annot _ | For _ | LetReg _ | Param _ -> assert false in
  aux f

let allsimplify f =
  let f = logic_simplify f in
(*   Myformat.printf "=============@.%a@.=================@." print f; *)
  Typing.formtyping f;
  let f = map_simplify f in
(*   Myformat.printf ">>>>>>>>>>>>>@.%a@.>>>>>>>>>>>>>>>>>@." print f; *)
  Typing.formtyping f;
  f
