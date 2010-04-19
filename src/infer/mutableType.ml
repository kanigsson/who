(******************************************************************************)
(*                                                                            *)
(*                      Who                                                   *)
(*                                                                            *)
(*       A simple VCGen for higher-order programs.                            *)
(*                                                                            *)
(*  Copyright (C) 2009, 2010, Johannes Kanig                                  *)
(*  Contact: kanig@lri.fr                                                     *)
(*                                                                            *)
(*  Who is free software: you can redistribute it and/or modify it under the  *)
(*  terms of the GNU Lesser General Public License as published by the Free   *)
(*  Software Foundation, either version 3 of the License, or any later        *)
(*  version.                                                                  *)
(*                                                                            *)
(*  Who is distributed in the hope that it will be useful, but WITHOUT ANY    *)
(*  WARRANTY; without even the implied warranty of MERCHANTABILITY or         *)
(*  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public      *)
(*  License for more details.                                                 *)
(*                                                                            *)
(*  You should have received a copy of the GNU Lesser General Public License  *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>      *)
(******************************************************************************)

module Uf = Unionfind

exception UndeterminedType

type ty =
  | U
  | Const of Const.ty
  | Tuple of t list
  | Arrow of t * t * rw
  | PureArr of t * t
  | App of Name.t * t list
  | Ref of r * t
  | Map of effect
and t = ty Uf.t
and r = rnode Uf.t
and rnode =
  | RU
  | RT of Name.t
and effect = r list * Name.S.t
and rw = effect * effect

let is_compound x =
  match Uf.desc x with
  | Const _ | Ref _ | Map _ | App _ | U -> false
  | Tuple _ | Arrow _ | PureArr _ -> true

let hash_effect (rl,s) =
  ExtList.hash Uf.hash (Name.hash_set s) rl

let hash_rw (e1,e2) = Hash.combine2 6 (hash_effect e1) (hash_effect e2)

let hash_ty t =
  match t with
  | U -> 1
  | Const c -> Const.hash_t c
  | Tuple l -> ExtList.hash Uf.hash 1 l
  | Ref (r,t) -> Hash.combine2 2 (Uf.hash r) (Uf.hash t)
  | Map e -> hash_effect e
  | App (n,i) ->
      Hash.combine 3 (ExtList.hash Uf.hash (Name.hash n) i)
  | Arrow (t1,t2,e) ->
      Hash.combine3 4 (Uf.hash t1) (Uf.hash t2) (hash_rw e)
  | PureArr (t1,t2) ->
      Hash.combine2 5 (Uf.hash t1) (Uf.hash t2)

let equal_r r1 r2 =
  match Uf.desc r1, Uf.desc r2 with
  | RU, RU -> Uf.equal r1 r2
  | RU, RT _ | RT _, RU -> false
  | RT n1, RT n2 -> Name.equal n1 n2

let equal_effect (r1,e1) (r2,e2) =
  Effect.s_equal e1 e2 && ExtList.equal_unsorted equal_r r1 r2

let equal_rw (a1,a2) (b1,b2) =
  equal_effect a1 b1 && equal_effect a2 b2

let equal_ty t1 t2 =
  match t1, t2 with
  (* two unification variables are always different *)
  | U, U -> false
  | Const c1, Const c2 -> Const.equal_t c1 c2
  | Tuple l1, Tuple l2 -> ExtList.equal Uf.equal l1 l2
  | Ref (r1,t1), Ref (r2,t2) -> Uf.equal r1 r2 && Uf.equal t1 t2
  | Map e1, Map e2 -> equal_effect e1 e2
  | App (n1,i1), App (n2,i2) ->
      Name.equal n1 n2 && ExtList.equal Uf.equal i1 i2
  | Arrow (t1a, t1b, e1), Arrow (t2a, t2b, e2) ->
      Uf.equal t1a t2a && Uf.equal t1b t2b && equal_rw e1 e2
  | PureArr (t1a, t1b), PureArr (t2a, t2b) ->
      Uf.equal t1a t2a && Uf.equal t1b t2b
  | _, _ -> false

module HBty = struct
  type t = ty
  let hash = hash_ty
  let equal = equal_ty
end

module HBe = struct
  type t = effect
  let hash = hash_effect
  let equal = equal_effect
end

module Hty = Hashtbl.Make(HBty)
module He = Hashtbl.Make(HBe)

let new_ty () = Uf.fresh U
let mkt t = Uf.fresh t

module Print = struct
  open Myformat

  let rec inst fmt i =
    Inst.print ~kind:`Who ~intype:true ty region effect fmt i

  and ty fmt (x : t) =
    let mayp fmt t = if is_compound t then paren ty fmt t else ty fmt t in
    match Uf.desc x with
    | U -> fprintf fmt "%d" (Uf.tag x)
    | Tuple tl ->
        list (fun fmt () -> fprintf fmt " *@ ") mayp fmt tl
    | Ref (r,t) -> fprintf fmt "ref(%a,%a)" region r ty t
    | PureArr (t1,t2) -> fprintf fmt "%a ->@ %a" mayp t1 ty t2
    | Map e -> fprintf fmt "<%a>" effect_no_sep e
    | Const c -> Const.print_ty `Who fmt c
    | App (v,i) -> fprintf fmt "%a%a" Name.print v (list comma ty) i
    | Arrow (t1,t2,eff) ->
        fprintf fmt "%a ->{%a} %a" mayp t1 rw eff ty t2
  and region fmt x =
    match Uf.desc x with
    | RU -> fprintf fmt "%d" (Uf.tag x)
    | RT n -> Name.print fmt n
  and region_list fmt l = list space region fmt l
  and effect_no_sep fmt (rl,el) =
    fprintf fmt "%a|" region_list rl;
    Name.print_set fmt el;
  and effect fmt e = fprintf fmt "{%a}" effect_no_sep e
  and rw fmt (e1,e2) = fprintf fmt "%a + %a" effect e1 effect e2
end

let memo =
  let h = Hty.create 17 in
  fun t ->
    try Uf.find (Hty.find h t)
    with Not_found ->
      let n = mkt t in
      Hty.add h t n; n

let parr t1 t2 = memo (PureArr (t1,t2))
let arrow t1 t2 e = memo (Arrow (t1,t2,e))
let tuple tl = memo (Tuple tl)
let ref_ r t = memo (Ref (r,t))
let var s = memo (App (s,[]))
let map e = memo (Map e)
let app v i = memo (App (v,i))

let eff_empty = [], Name.S.empty
let rw_empty = eff_empty, eff_empty

let new_r () = Uf.fresh RU
let from_region =
  let h = Name.H.create 17 in
  fun r ->
    try Name.H.find h r
    with Not_found ->
      let n = Uf.fresh (RT r) in
      Name.H.add h r n; n

let r_equal a b = Uf.tag a = Uf.tag b

let rremove (r,e) rl =
  List.filter (fun x -> not (ExtList.mem r_equal x rl)) r, e

let eff_union (r1,e1) (r2,e2) =
  ExtList.union r_equal r1 r2, Name.S.union e1 e2

let eff_union3 a b c = eff_union a (eff_union b c)

let rw_union (ea1, ea2) (eb1,eb2) =
  eff_union ea1 eb1, eff_union ea2 eb2

let rw_union3 e1 e2 e3 = rw_union e1 (rw_union e2 e3)

let rw_rremove (e1,e2) rl =
  rremove e1 rl, rremove e2 rl


let const =
  let h = Hashtbl.create 5 in
  List.iter (fun c -> Hashtbl.add h c (mkt (Const c)))
  [ Const.TInt ; Const.TProp ];
  fun c -> Hashtbl.find h c

let prop = const Const.TProp
let bool () = var (Predefty.var (Predefty.Identifier.bool_id))
let unit () = var (Predefty.var (Predefty.Identifier.unit_id))
let int = const Const.TInt

let rec from_ty (x : Ty.t) =
  match x with
  | Ty.Const c -> const c
  | Ty.Arrow (t1,t2,e) ->
      arrow (from_ty t1) (from_ty t2) (from_rw e)
  | Ty.Tuple tl -> tuple (List.map from_ty tl)
  | Ty.Ref (r,t) -> ref_ (from_region r) (from_ty t)
  | Ty.Map e -> map (from_effect e)
  | Ty.PureArr (t1,t2) -> parr (from_ty t1) (from_ty t2)
  | Ty.App (v,i) -> app v (List.map from_ty i)
and from_effect eff =
  let rl, e = Effect.to_u_effect eff in
  List.map from_region rl, e
and from_rw e =
  from_effect (Rw.reads e), from_effect (Rw.writes e)

let node_map ~f ~eff_fun ~rfun t : t =
  let rec aux t =
    let t = match Uf.desc t with
    | U | Const _ -> t
    | Tuple t -> tuple (List.map aux t)
    | PureArr (t1,t2) -> parr (aux t1) (aux t2)
    | Ref (r,t) -> ref_ (rfun r) (aux t)
    | Map e -> map (eff_fun e)
    | Arrow (t1,t2,e) ->
        arrow (aux t1) (aux t2) (rw_fun e)
    | App (n,i) -> app n (List.map aux i) in
    f t
  and rw_fun (e1,e2) = eff_fun e1, eff_fun e2 in
  aux t

let effect_subst h acc =
  (* substitute effect variables for effects in effects *)
  Name.H.fold (fun k v ((rl,e) as acc) ->
    if Name.S.mem k e then
      let e = Name.S.remove k e in
      eff_union v (rl,e)
    else acc
  ) h acc

let region_subst h r =
  match Uf.desc r with
  | RU -> r
  | RT reg ->
      try Name.H.find h reg
      with Not_found -> r

let r_effectsubst h (r,e) = List.map (region_subst h) r, e

let esubst evl el t =
  let table = Name.H.create 17 in
  begin try List.iter2 (fun v e -> Name.H.add table v e) evl el
  with Invalid_argument _ ->
    invalid_arg "esubst" end;
  node_map ~f:Misc.id ~eff_fun:(effect_subst table) ~rfun:Misc.id t

let rsubst rvl rl t =
  let table = Name.H.create 17 in
  begin try List.iter2 (fun v e -> Name.H.add table v e) rvl rl
  with Invalid_argument _ ->
    invalid_arg "rsubst" end;
  node_map ~f:Misc.id ~eff_fun:(r_effectsubst table)
           ~rfun:(region_subst table) t

let ty_subst h t =
  match Uf.desc t with
  | App (v,[]) ->
      begin try Name.H.find h v
      with Not_found -> t end
  | _ -> t

let tsubst tvl tl t =
  let table = Name.H.create 17 in
  begin try List.iter2 (fun v e -> Name.H.add table v e) tvl tl
  with Invalid_argument _ ->
    invalid_arg "rsubst" end;
  node_map ~f:(ty_subst table) ~eff_fun:Misc.id ~rfun:Misc.id t

let bh f l =
  let h = Name.H.create 3 in
  List.map (fun x -> let n = f () in Name.H.add h x n; n) l,h

let split t =
  match Uf.desc t with
  | PureArr (t1,t2) -> t1, t2
  | _ -> invalid_arg "split"

let nsplit =
  let rec aux acc t =
    try
      let t1,t2 = split t in
      aux (t1::acc) t2
    with Invalid_argument "split" -> List.rev acc, t
  in
  aux []

let refresh ((tvl, rvl, evl) : Ty.Generalize.t)
            ((tl,rl,el) : Ty.t list * Name.t list * Effect.t list) (t : t)
            : t * (t,r,effect) Inst.t  =
  let tn, th = bh new_ty tvl and rn, rh = bh new_r rvl in
  let el = List.map from_effect el in
  let t = esubst evl el t in
  let t = if tl = [] then t else tsubst tvl (List.map from_ty tl) t in
  let t = if rl = [] then t else rsubst rvl (List.map from_region rl) t in
  let f x =
    match Uf.desc x with
    | App (v,[]) ->
        begin try Name.H.find th v
        with Not_found -> x end
    | _ -> x in
  let rfun n =
    match Uf.desc n with
    | RT r -> begin try Name.H.find rh r with Not_found -> n end
    | _ -> n in
  let ersubst (rl,s) = List.map rfun rl, s in
  let nt = node_map ~f ~eff_fun:ersubst ~rfun t in
  nt, (tn,rn,el)

module HBt = struct
  type t' = t
  type t = t'
  let equal a b = Uf.tag a = Uf.tag b
  let hash = Uf.tag
end

module HBr = struct
  type t = r
  let equal a b = Uf.tag a = Uf.tag b
  let hash = Uf.tag
end

module Ht = Hashtbl.Make(HBt)

let to_region r =
  match Uf.desc r with
  | RU -> raise UndeterminedType
  | RT s -> s
let to_effect (r,e) = Effect.from_u_effect (List.map to_region r) e
let to_rw (e1,e2) = Rw.mk ~read:(to_effect e1) ~write:(to_effect e2)

let to_ty =
  let h = Ht.create 17 in
  let rec to_ty t =
    try Ht.find h t
    with Not_found ->
      let r =
        match Uf.desc t with
        | U -> raise UndeterminedType
        | Arrow (t1,t2,e) -> Ty.arrow (to_ty t1) (to_ty t2) (to_rw e)
        | Tuple tl -> Ty.tuple (List.map to_ty tl)
        | Const c -> Ty.const c
        | Ref (r,t) -> Ty.ref_ (to_region r) (to_ty t)
        | Map e -> Ty.map (to_effect e)
        | PureArr (t1,t2) -> Ty.parr (to_ty t1) (to_ty t2)
        | App (v,i) -> Ty.app v (List.map to_ty i) in
      Ht.add h t r;
      r in
  to_ty

let base_pre_ty eff = parr (map eff) prop
let base_post_ty e t = parr (map e) (parr (map e) (parr t prop))
let pretype a e = parr a (base_pre_ty e)
let posttype a b e = parr a (base_post_ty e b)
let prepost_type a b e =
  tuple [ pretype a e ; posttype a b e ]

let overapprox (e1,e2) = eff_union e1 e2

let to_logic_type t =
  node_map ~rfun:Misc.id ~eff_fun:Misc.id ~f:(fun t ->
    match Uf.desc t with
    | Arrow (t1,t2,e) -> prepost_type t1 t2 (overapprox e)
    | _ -> t) t

let print = Print.ty
let print_region = Print.region
let region_list = Print.region_list
let print_effect = Print.effect
let print_rw = Print.rw
