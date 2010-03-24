module Uf = Unionfind
(* TODO Hash-consing *)
(* TODO rewrite so that this type is a reimplemenation, no recursive knot *)
(* TODO separate functionality for refresh and from_ty *)

type ty =
  | U
  | T of (t,r, effect) Ty.t'
and t = ty Uf.t
and r = rnode Uf.t
and rnode =
  | RU
  | RT of Name.t
and effect = r list * Name.S.t

let new_ty () = Uf.fresh U
let mkt t = Uf.fresh (T t)
let arrow t1 t2 e c = mkt (Ty.Arrow (t1,t2,e,c))
let tuple tl = mkt (Ty.Tuple tl)
let ref_ r t = mkt (Ty.Ref (r,t))
let mkr r = Uf.fresh (RT r)
let new_r () = Uf.fresh RU
let var s = mkt (Ty.App (s,([],[],[])))
let map e = mkt (Ty.Map e)
let app v i = mkt (Ty.App (v,i))
let parr t1 t2 = mkt (Ty.PureArr (t1,t2))

let eff_empty = [], Name.S.empty

let r_equal r1 r2 =
  match Uf.desc r1, Uf.desc r2 with
  | RU, RU -> Uf.equal r1 r2
  | RU, RT _ | RT _, RU -> false
  | RT n1, RT n2 -> Name.equal n1 n2

let rremove (r,e) rl =
  List.filter (fun x -> not (Misc.list_mem r_equal x rl)) r, e
let eff_union (r1,e1) (r2,e2) =
  Misc.list_union r_equal r1 r2, Name.S.union e1 e2

let eff_union3 a b c = eff_union a (eff_union b c)


let const =
  let h = Hashtbl.create 5 in
  List.iter (fun c -> Hashtbl.add h c (mkt (Ty.Const c)))
  [ Const.TInt ; Const.TProp ];
  fun c -> Hashtbl.find h c

let prop = const Const.TProp
let bool = var Predefty.bool_var
let unit = var Predefty.unit_var
let int = const Const.TInt

module HT = Hashtbl

let bh f l =
  let h = Hashtbl.create 3 in
  List.map (fun x -> let n = f () in Hashtbl.add h x n; n) l,h

let ymemo ff =
  let h = Hashtbl.create 17 in
  let rec f x =
    try Hashtbl.find h x
    with Not_found ->
      let z = ff f x in
      Hashtbl.add h x z; z in
  f

let to_uf_node (tl,rl,evl) el (x : Ty.t ) =
  let x = Ty.elsubst evl el x in
  let tn,th = bh new_ty tl and rn,rh = bh new_r rl in
  let rec aux f (x : Ty.t) : t =
    let Ty.C x = x in
    match x with
    | Ty.Const c -> const c
    | Ty.Arrow (t1,t2,e, c) ->
        arrow (f t1) (f t2) (eff e) (List.map auxr c)
    | Ty.Tuple tl -> tuple (List.map f tl)
    | Ty.Ref (r,t) -> ref_ (auxr r) (f t)
    | Ty.Map e -> map (eff e)
    | Ty.PureArr (t1,t2) -> parr (f t1) (f t2)
    | Ty.App (v,([],[],[])) ->
        begin try HT.find th v with Not_found -> var v end
    | Ty.App (v,i) -> app v (Inst.map f auxr eff i)
  and real x = ymemo aux x
  and auxr r = try HT.find rh r with Not_found -> mkr r
  and eff (ef : Effect.t) : effect =
    let rl, e = Effect.to_u_effect ef in
    List.map auxr rl, e in
  real x, (tn, rn, List.map eff el)

let to_uf_rnode r = mkr r
let to_uf_enode ef =
  let rl, e = Effect.to_u_effect ef in
  List.map to_uf_rnode rl, e

let sto_uf_node x = fst (to_uf_node Ty.Generalize.empty [] x)

module H = Hashtbl.Make (struct
                           type t' = t
                           type t = t'
                           let equal a b = Uf.tag a = Uf.tag b
                           let hash = Uf.tag
                         end)

let to_ty, to_eff, to_r =
  let h = H.create 127 in
  let rec ty' = function
    | Ty.Arrow (t1,t2,e,cap) ->
        Ty.caparrow (ty t1) (ty t2) (eff e) (List.map rv cap)
    | Ty.Tuple tl -> Ty.tuple (List.map ty tl)
    | Ty.Const c -> Ty.const c
    | Ty.Ref (r,t) -> Ty.ref_ (rv r) (ty t)
    | Ty.Map e -> Ty.map (eff e)
    | Ty.PureArr (t1,t2) -> Ty.parr (ty t1) (ty t2)
    | Ty.App (v,i) -> Ty.app v (Inst.map ty rv eff i)
  and ty x =
    try H.find h x
    with Not_found ->
      match Unionfind.desc x with
      | U ->
          failwith "cannot determine the type of some object, please help me"
      | T t ->
          let r = ty' t in
          H.add h x r; r
  and rv r =
    match Uf.desc r with
    | RU -> assert false
    | RT s -> s
  and eff (r,e) = Effect.from_u_effect (List.map rv r) e in
  ty, eff, rv

let base_pre_ty eff = parr (map eff) prop
let base_post_ty eff t = parr (map eff) (parr (map eff) (parr t prop))
let pretype a e = parr a (base_pre_ty e)
let posttype a b e = parr a (base_post_ty e b)
let prepost_type a b e = tuple [ pretype a e ; posttype a b e ]

let to_logic_type t =
  let rec aux t =
    match Uf.desc t with
    | U -> t
    | T ty ->
        match ty with
        | (Ty.Const _ | Ty.Map _) -> t
        | Ty.Tuple tl -> tuple (List.map aux tl)
        | Ty.PureArr (t1,t2) -> parr (aux t1) (aux t2)
        | Ty.Arrow (t1,t2,e,_) -> prepost_type (aux t1) (aux t2) e
        | Ty.Ref (x,t) -> ref_ x (aux t)
        | Ty.App (v,i) -> app v (Inst.map aux Misc.id Misc.id i)
  in
  aux t


let refresh (tvl, rvl, evl) el t = assert false

