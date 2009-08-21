open Vars
module VM = Var.M

type t' = 
  | Var of Var.t * (Fty.t, RVar.t, Effect.t) Inst.t
  | Const of Const.t
  | App of t * t * [ `Infix | `Prefix ]
  | Binder of [ `FA | `EX | `LAM ] *  Fty.t * varbind
  | Gen of letbind
  | PolyLet of letbind * varbind
  | Let of t * varbind
  | Restrict of Effect.t * t
  | Combine of t * t
  | Get of RVar.t * t
  | Set of RVar.t * t * t
  | Empty
and varbind = t Var.bind
and letbind = t Fty.Generalize.bind
and generalize = Fty.Generalize.t
and t = { v : t'; t : Fty.t ; hint : string option ; loc : Loc.loc }

let get_sub f = f.v
let get_type f = f.t

let set_type t f = {f with t = t }

let with_rec f t = { t with v = f t.v }

let domain f = Fty.domain (get_type f)

let lmk t v loc = { v = v; t = t; hint = None; loc = loc} 
let var x i ty = lmk ty (Var (x,i))
let var' x i = Var (x,i)
let svar l = var l Inst.empty
let const c = lmk (Fty.const (Const.type_of_constant c)) (Const c)
let void = lmk Fty.unit (Const Const.Void)

(*
let rbase loc l r = lookup r (svar l loc) loc
let ebase loc l e = svar l loc
*)

module Debprint =
struct
  open Myformat


  let evar_list fmt l = 
    print_list space (fun fmt _ -> semi fmt ()) fmt l

  let use fmt (r,t) = 
    fprintf fmt "(%a : %a)" RVar.print r Fty.print t
  let use_list = print_list space use

  let rec print_head fmt x = 
    match get_sub x with
    | Const c -> Const.print fmt c
    | Var (v,i) when Inst.is_empty i -> Var.print fmt v
    | Var (v,i) -> 
        fprintf fmt "%a %a" Var.print v 
          (Inst.print Fty.print RVar.print Effect.print ) i
    | App (t1,_,`Infix) ->
        begin match get_sub t1 with
        | App (op,_,_) -> fprintf fmt "(- %a )" print_head op
        | _ -> assert false
        end
    | App (_,_,_) -> fprintf fmt "app"
    | Binder (k,_,_) -> fprintf fmt "(%a)" Const.quant k
    | PolyLet (_,_) -> pp_print_string fmt "<plet>"
    | Let (_,_) -> pp_print_string fmt "<let>"
    | Set (r,_,_) -> fprintf fmt "set(%a)" RVar.print r 
    | Get (r,_) -> fprintf fmt "get(%a)" RVar.print r 
    | Combine (_,_) -> fprintf fmt "combine"
    | Restrict (eff,_) -> fprintf fmt "restrict(%a)" Effect.print eff 
    | Gen _ -> fprintf fmt "gener"
    | Empty -> fprintf fmt "empty" 

end
let map ~varfun ~effectfun ~rvarfun 
              ~tyfun ~varbindfun ~genbindfun f = 
    let rec aux = function
      | (Const _ as t) -> t
      | Var (v,i) -> 
          varfun v (Inst.map tyfun rvarfun effectfun i)
      | App (t1,t2,p) -> App (aux_node t1, aux_node t2, p)
      | Binder (knd, t, b) -> Binder (knd, tyfun t, varbindfun b)
      | PolyLet (tlb,b) -> PolyLet (genbindfun tlb, varbindfun b)
      | Gen tlb -> Gen (genbindfun tlb)
      | Set (r,f1,f2) -> Set (rvarfun r, aux_node f1, aux_node f2)
      | Get (r,f) -> Get (rvarfun r, aux_node f)
      | Combine (f1,f2) -> Combine (aux_node f1, aux_node f2)
      | Restrict (eff,f) -> Restrict (effectfun eff, aux_node f)
      | Let (f,b) -> Let (aux_node f, varbindfun b)
      | Empty -> Empty
    and aux_node f = { f with v = aux f.v; t = tyfun f.t; } in 
    aux_node f

let rec refresh s t = 
  map 
    ~varfun:(fun x i -> Var (Var.refresh s x, i))
    ~effectfun:(Effect.refresh s)
    ~tyfun:(Fty.refresh s)
    ~rvarfun:(RVar.refresh s)
    ~varbindfun:(Var.refresh_bind s)
    ~genbindfun:(EffVar.refresh_listbind s)
    t

let open_bind = Var.open_bind refresh
let open_bind_with = Var.open_with refresh
let close_bind = Var.close_bind
let open_tygen = TyVar.open_listbind refresh
let open_tygen_with = TyVar.list_open_with refresh
let open_evgen = EffVar.open_listbind refresh
let open_evgen_with = EffVar.list_open_with refresh
let open_letgen c = Fty.Generalize.open_bind refresh c
let open_letgen_with g c = Fty.Generalize.open_bind_with refresh g c

let close_evgen = EffVar.close_listbind
let close_tygen = TyVar.close_listbind
let close_letgen = Fty.Generalize.close_bind

let open_rbind = RVar.open_listbind refresh
let open_rbind_with = RVar.list_open_with refresh
let close_rbind = RVar.close_listbind

let get_top_binders k t = 
  let rec aux acc = function
    | Binder (k', t,b) when k = k' ->
        let x,f = open_bind b in
        aux ((x,t)::acc) f.v
    | f -> List.rev acc,f in
  aux [] t
    
module Print = 
struct
  open Myformat

  let paren f fmt x = fprintf fmt "(%a)" f x
  let fbinder fmt (v,t) = fprintf fmt "%a : %a"  Var.print v Fty.print t
  let fbind_paren = paren fbinder

  let is_f_compound x = 
    match get_sub x with
    | Const _ | Var _ | Empty -> false
    | App _ | Binder _ | PolyLet _ | Gen _  | Let _
    | Set _ | Get _ | Combine _ | Restrict _ -> true

  let evar_list = print_list space EffVar.print
  let tyvar_list = print_list space TyVar.print
  let rvar_list fmt (rl,tl)= 
    let l = List.map2 (fun a b -> a,b) rl tl in
    let print_elt fmt (r,t) = fprintf fmt "%a : %a" RVar.print r Fty.print t in
    print_list space print_elt fmt l
    

  let rec formula fmt x =
    match x with
    | Empty -> fprintf fmt "empty"
    | Const c -> Const.print fmt c
    | Var (v,i) when Inst.is_empty i -> fprintf fmt "%a" Var.print v
    | Var (v,i) -> 
        fprintf fmt "%a %a" Var.print v 
          (Inst.print Fty.print RVar.print Effect.print) i
    | App (f1,f2,`Infix) ->
        begin match get_sub f1 with
        | App (op,f1,_) -> 
            fprintf fmt "(@[%a@ %a@ %a@])" form f1 form op form f2
        | _ -> assert false
        end
    | App (f1,f2,_) -> 
        let p2 = if is_f_compound f2 then paren form else form in
        fprintf fmt "@[%a@ %a@]" form f1 p2 f2
    | Binder (k,_,_) -> 
        let bl,f = get_top_binders k x in
        fprintf fmt "(@[%a %a %a@ %a@])" Const.quant k 
          (print_list space fbind_paren) bl Const.quantsep k formula f
    | Gen l ->
        let g,f = open_letgen l in
        fprintf fmt "forall %a.@ %a" Fty.Generalize.print g form f
    | PolyLet (lg,vb) -> 
        let g,v = open_letgen lg in
        let x,f = open_bind vb in
        fprintf fmt "%a[%a.%a|->%a]" 
          form f Fty.Generalize.print g Var.print x form v
    | Let (f,vb) -> 
        let x,body = open_bind vb in
        fprintf fmt "let %a = %a in %a" Var.print x form f form body
    | Set (r,v,m) -> fprintf fmt "(set %a %a %a)" RVar.print r form v form m
    | Get (r,m) -> fprintf fmt "get %a %a" RVar.print r form m
    | Combine (m1,m2) -> fprintf fmt "(combine %a %a)" form m1 form m2
    | Restrict (eff,m) -> fprintf fmt "(restrict(%a) %a)" Effect.print eff form m
  and form fmt f = formula fmt (get_sub f)

end

let open_close_map ~varfun ~effectfun ~tyfun ~rvarfun t =
  let rec aux t = 
    map ~varfun ~effectfun ~tyfun ~rvarfun
      ~varbindfun:(fun b ->
        let x,f = open_bind b in
        close_bind x (aux f))
      ~genbindfun:(fun b ->
        let g,f = open_letgen b in
        close_letgen g (aux f))
      t
  in
  aux t

let effsubst ev eff f = 
  open_close_map
    ~varfun:var'
    ~effectfun:(Effect.effsubst ev eff)
    ~tyfun:(Fty.effsubst ev eff)
    ~rvarfun:Misc.id
    f

let rec tysubst tv t f = 
  open_close_map
    ~varfun:var'
    ~effectfun:Misc.id
    ~tyfun:(Fty.tysubst tv t)
    ~rvarfun:Misc.id
    f

let rec rsubst r nr f = 
  open_close_map
    ~varfun:var'
    ~effectfun:(Effect.rsubst r nr)
    ~rvarfun:(fun k -> if RVar.equal k r then nr else k)
    ~tyfun:(Fty.rsubst r nr)
    f

let ltysubst = List.fold_right2 tysubst
let leffsubst = List.fold_right2 effsubst 
let lrsubst = List.fold_right2 rsubst

let subst x v e =
  open_close_map
    ~varfun:(fun z i -> 
        if Var.equal z x then v i else Var (z,i))
    ~effectfun:Misc.id
    ~tyfun:Misc.id
    ~rvarfun:Misc.id
    e

let polsubst (tl,rl,el) x v f = 
  let builder (tyl, nrl, effl) = 
    get_sub (lrsubst rl nrl (leffsubst el effl (ltysubst tl tyl v))) in
  subst x builder f

let varbind kind x t f = 
  let l = close_bind x f in
  let ty = 
    match kind with
    | `LAM -> Fty.arr t (get_type f)
    | `FA | `EX -> Fty.prop
  in
  lmk ty (Binder (kind,t,l))

let varbindho ?name kind t f loc = 
  let x = match name with 
          | None -> Var.new_anon ()
          | Some s -> Var.from_string s in
  let x' = svar x t loc in
  varbind kind x t (f x') loc

let massbind kind l f loc = 
  List.fold_right (fun (x,t) acc -> varbind kind x t acc loc) l f

let lam x t f = varbind `LAM x t f
let forall x t f = varbind `FA x t f

let lamho ?name t f = varbindho ?name `LAM t f
let forallho ?name t f = varbindho ?name `FA t f

let mapbind kind x eff f = varbind kind x (Fty.mkmap eff) f 
let mapbindho ?name kind eff f = varbindho ?name kind (Fty.mkmap eff) f 

let efflam x eff f = mapbind `LAM x eff f
let effFA x eff f = mapbind `FA x eff f
let efflamho ?name eff f = mapbindho ?name `LAM eff f
let effFAho ?name eff f = mapbindho ?name `FA eff f

let postho t1 t2 eff f loc = 
  lamho t1
    (fun x ->
      efflamho eff
        (fun old ->
          efflamho eff
            (fun cur ->
              lamho t2 (fun r -> f x old cur r) loc) loc) loc) loc

let preho t eff f loc =
  lamho t (fun x -> efflamho eff (fun cur -> f x cur) loc) loc

let get r m t = lmk t (Get (r,m))
let set r v m = lmk (get_type m) (Set (r,v,m))
let map_empty = lmk (Fty.mkmap (Effect.empty)) Empty 
let restrict eff t = 
  lmk (Fty.mkmap (Effect.intersection eff (domain t))) (Restrict (eff,t))

let combine t1 t2 =  
  let e1 = domain t1 and e2 = domain t2 in
  lmk (Fty.mkmap (Effect.union e1 e2)) (Combine (t1,t2))

let true_ = lmk Fty.prop (Const Const.Ptrue)
let app ?(kind=`Prefix) t1 t2 loc = 
  let t = Fty.result (get_type t1) in
  lmk t (App (t1,t2,kind)) loc

let app2 ?k1 ?k2 t1 t2 t3 loc = app ?kind:k2 (app ?kind:k1 t1 t2 loc) t3 loc

let infix = app2 ~k1:`Prefix ~k2:`Infix
let predef_var s tl loc = 
  let v, tvl, t = Fty.get_predef_var s in
  var v (tl, [], []) (Fty.ltysubst tvl tl t) loc

let spredef_var s loc = predef_var s [] loc

let impl f1 f2 loc =
  match get_sub f1, get_sub f2 with
  | Const Const.Ptrue, _ -> f2
  | _, Const Const.Ptrue -> f1
  | Const Const.Pfalse, _ -> true_ loc
  | _, _ -> infix (spredef_var "->" loc) f1 f2 loc

let false_ = lmk Fty.prop (Const Const.Pfalse)

let applist l loc = 
  match l with
  | [] | [ _ ] -> failwith "not enough arguments given"
  | a::b::rest ->
      List.fold_left (fun acc x -> app acc x loc) (app a b loc) rest

let and_ f1 f2 loc = 
  match get_sub f1, get_sub f2 with
  | Const Const.Ptrue, _ -> f2
  | _, Const Const.Ptrue -> f1
  | Const Const.Pfalse, _  | _, Const Const.Pfalse -> false_ loc
  | _ -> infix (spredef_var "/\\" loc) f1 f2 loc

let andlist l loc = 
  match l with
  | [] | [ _ ] -> failwith "not enough arguments given"
  | a::b::rest ->
      List.fold_left (fun acc x -> and_ acc x loc) (and_ a b loc) rest

let tuple f1 f2 loc = 
  infix (predef_var "," [get_type f1; get_type f2] loc) f1 f2 loc

let not_ f loc = app (spredef_var "~" loc) f loc

let destruct_infix' = function
  | App ({ v = App ({ v = Var (v,_)},t1,_) },t2,`Infix) -> Some (v,t1,t2)
  | _ -> None

let destruct_infix x = destruct_infix' (get_sub x)

let pre f loc = 
  match destruct_infix f with
  | Some ({Var.name = Some ","},t1,_) -> t1
  | _ ->
      match get_type f with
      | `U `Tuple (t1,t2) -> app (predef_var "fst" [t1;t2] loc) f loc
      | _ -> assert false

let post f loc = 
  match destruct_infix f with
  | Some ({Var.name = Some ","},_,t2) -> t2
  | _ ->
      match get_type f with
      | `U `Tuple (t1,t2) -> app (predef_var "snd" [t1;t2] loc) f loc
      | _ -> assert false

let gen g f loc = 
  match get_sub f with
  | Const Const.Ptrue -> f
  | _ when Fty.Generalize.is_empty g -> f
  | _ -> lmk (get_type f) (Gen (close_letgen g f)) loc
let evgen gl = gen ([],[],gl)
let rgen gl = gen ([],gl,[])
let tygen gl = gen (gl,[],[])

let polylet_ g x v f loc = 
  lmk (get_type f) (PolyLet (close_letgen g v, close_bind x f)) loc

let let_ v x f loc = 
  lmk (get_type f) (Let (v, close_bind x f)) loc

let eq f1 f2 loc = infix (predef_var "=" [get_type f1] loc) f1 f2 loc

let btrue = lmk Fty.bool (Const Const.Btrue)
let bfalse = lmk Fty.bool (Const Const.Bfalse)

let one = 
  lmk Fty.int (Const (Const.Int (Big_int.unit_big_int)))

module LocImplicit = struct

  type t' = Loc.loc -> t
  let unary c f loc = c (f loc) loc
  let binary c f1 f2 loc = c (f1 loc) (f2 loc) loc

  let lam x t f = unary (lam x t) f
  let efflam x e f = unary (efflam x e) f
  let effFA x e f = unary (effFA x e) f
  let forall x t f = unary (forall x t) f
  let impl f1 f2 = binary impl f1 f2
  let app f1 f2 = binary app f1 f2
  let and_ f1 f2 = binary and_ f1 f2
  let tuple f1 f2 = binary tuple f1 f2
  let eq f1 f2 = binary eq f1 f2
  let get r f t = unary (fun f -> get r f t) f
  let set r v f = binary (set r) v f
  let combine t1 t2 = binary combine t1 t2
  let restrict eff t = unary (restrict eff) t
  let applist fl loc = applist (List.map (fun f -> f loc) fl) loc
  let andlist fl loc = andlist (List.map (fun f -> f loc) fl) loc
  let true_ = true_
  let btrue = btrue
  let bfalse = bfalse
  let void = void
  let pre f = unary pre f
  let post f = unary post f
  let var = var
  let svar v = var v Inst.empty
  let evgen vl f = unary (evgen vl) f
  let rgen vl f = unary (rgen vl) f
  let tygen vl f = unary (tygen vl) f
  let polylet_ g x v f = binary (polylet_ g x) v f
  let let_ v x f loc = let_ (v loc) x (f loc) loc
  let lamho ?name t f loc  = 
    lamho ?name t ((fun v -> f (fun loc -> { v with loc = loc}) loc)) loc
  let lamho2 t1 t2 f loc = 
    lamho t1 (fun v1 -> lamho t2 (fun v2 -> f v1 v2)) loc
  let lamho3 ?name1 ?name2 ?name3 t1 t2 t3 f loc = 
    lamho ?name:name1 t1 (fun v1 -> 
      lamho ?name:name2 t2 (fun v2 -> 
        lamho ?name:name3 t3 (fun v3 -> f v1 v2 v3))) loc
  let forallho ?name t f loc  = 
    forallho ?name t ((fun v -> f (fun loc -> { v with loc = loc}) loc)) loc
  let effFAho ?name eff f loc  = 
    effFAho ?name eff ((fun v -> f (fun loc -> { v with loc = loc}) loc)) loc
  let efflamho ?name eff f loc = 
    efflamho ?name eff ((fun v -> f (fun loc -> { v with loc = loc}) loc)) loc
  let efflamho2 eff1 eff2 f =
    efflamho eff1 (fun v -> efflamho eff2 (fun v2 -> f v v2))

  let predef_binop op a b = applist [spredef_var op; a; b]
  let le = predef_binop "<="
  let lt = predef_binop "<"
  let max = predef_binop "max"
  let min = predef_binop "min"
  let succ a = predef_binop "+" a one
  let prev a = predef_binop "-" a one
  let preho t eff f = lamho t (fun x -> efflamho eff (fun cur -> f x cur))
  let postho t1 t2 eff f = 
    lamho t1 (fun x -> 
      efflamho2 eff eff (fun old cur -> lamho t2 (fun r -> f x old cur r)))

  let encl v1 i v2 = and_ (le v1 i) (le i v2)

  let subst x v e loc = subst x (fun i -> get_sub (v i loc)) (e loc)
end

let ibinary f a b = f (fun _ -> a) (fun _ -> b)
let le = ibinary LocImplicit.le
let lt = ibinary LocImplicit.lt

let print = Print.form
let print_head = Debprint.print_head
let print_node = Print.formula

