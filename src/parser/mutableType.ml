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

type ty =
  | U
  | Const of Const.ty
  | Tuple of t list
  | Arrow of t * t * effect * r list
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

let is_compound x =
  match Uf.desc x with
  | Const _ | Ref _ | Map _ | App _ | U -> false
  | Tuple _ | Arrow _ | PureArr _ -> true

let hash_effect (rl,s) =
  ExtList.hash Uf.hash (Name.hash_set s) rl

let hash_ty t =
  match t with
  | U -> 1
  | Const c -> Const.hash_t c
  | Tuple l -> ExtList.hash Uf.hash 1 l
  | Ref (r,t) -> Hash.combine2 2 (Uf.hash r) (Uf.hash t)
  | Map e -> hash_effect e
  | App (n,i) ->
      Hash.combine 3 (ExtList.hash Uf.hash (Name.hash n) i)
  | Arrow (t1,t2,e,rl) ->
      Hash.combine3 4 (Uf.hash t1) (Uf.hash t2)
        (ExtList.hash Uf.hash (hash_effect e) rl)
  | PureArr (t1,t2) ->
      Hash.combine2 5 (Uf.hash t1) (Uf.hash t2)

let equal_r r1 r2 =
  match Uf.desc r1, Uf.desc r2 with
  | RU, RU -> Uf.equal r1 r2
  | RU, RT _ | RT _, RU -> false
  | RT n1, RT n2 -> Name.equal n1 n2

let equal_effect (r1,e1) (r2,e2) =
  Effect.s_equal e1 e2 && ExtList.equal_unsorted equal_r r1 r2

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
  | Arrow (t1a, t1b, e1, rl1), Arrow (t2a, t2b, e2, rl2) ->
      Uf.equal t1a t2a && Uf.equal t1b t2b && ExtList.equal Uf.equal rl1 rl2 &&
        equal_effect e1 e2
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
    | Map e -> fprintf fmt "<%a>" effect e
    | Const c -> Const.print_ty `Who fmt c
    | App (v,i) -> fprintf fmt "%a%a" Name.print v (list comma ty) i
    | Arrow (t1,t2,eff,cap) ->
        fprintf fmt "%a ->{%a%a} %a" mayp t1 effect eff maycap cap ty t2
  and maycap fmt = function
    | [] -> ()
    | l -> fprintf fmt "|%a" region_list l
  and region fmt x =
    match Uf.desc x with
    | RU -> fprintf fmt "%d" (Uf.tag x)
    | RT n -> Name.print fmt n
  and region_list fmt l = list space region fmt l
  and effect fmt (rl,el) =
    fprintf fmt "{%a|" region_list rl;
    Name.S.iter (Name.print fmt) el;
    pp_print_string fmt "}"
end

let memo =
  let h = Hty.create 17 in
  fun t ->
    try Uf.find (Hty.find h t)
    with Not_found ->
      let n = mkt t in
      Hty.add h t n; n

let parr t1 t2 = memo (PureArr (t1,t2))
let arrow t1 t2 e c = memo (Arrow (t1,t2,e,c))
let tuple tl = memo (Tuple tl)
let ref_ r t = memo (Ref (r,t))
let var s = memo (App (s,[]))
let map e = memo (Map e)
let app v i = memo (App (v,i))

let eff_empty = [], Name.S.empty

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
  | Ty.Arrow (t1,t2,e, c) ->
      arrow (from_ty t1) (from_ty t2) (from_effect e) (List.map from_region c)
  | Ty.Tuple tl -> tuple (List.map from_ty tl)
  | Ty.Ref (r,t) -> ref_ (from_region r) (from_ty t)
  | Ty.Map e -> map (from_effect e)
  | Ty.PureArr (t1,t2) -> parr (from_ty t1) (from_ty t2)
  | Ty.App (v,i) -> app v (List.map from_ty i)
and from_effect eff =
  let rl, e = Effect.to_u_effect eff in
  List.map from_region rl, e

let node_map ~f ~eff_fun ~rfun t : t =
  let rec aux t =
    let t = match Uf.desc t with
    | U | Const _ -> t
    | Tuple t -> tuple (List.map aux t)
    | PureArr (t1,t2) -> parr (aux t1) (aux t2)
    | Ref (r,t) -> ref_ (rfun r) (aux t)
    | Map e -> map (eff_fun e)
    | Arrow (t1,t2,e,rl) ->
        arrow (aux t1) (aux t2) (eff_fun e) (List.map rfun rl)
    | App (n,i) -> app n (List.map aux i) in
    f t in
  aux t

let effect_subst h acc =
  (* substitute effect variables for effects in effects *)
  Name.H.fold (fun k v ((rl,e) as acc) ->
    if Name.S.mem k e then
      let e = Name.S.remove k e in
      eff_union v (rl,e)
    else acc
  ) h acc

let esubst evl el t =
  let table = Name.H.create 17 in
  begin try List.iter2 (fun v e -> Name.H.add table v e) evl el
  with Invalid_argument _ ->
    invalid_arg "esubst" end;
  node_map ~f:Misc.id ~eff_fun:(effect_subst table) ~rfun:Misc.id t

let bh f l =
  let h = Name.H.create 3 in
  List.map (fun x -> let n = f () in Name.H.add h x n; n) l,h

let refresh (tvl, rvl, evl) el t =
  let tn, th = bh new_ty tvl and rn, rh = bh new_r rvl in
  let el = List.map from_effect el in
  let t = esubst evl el t in
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
  | RU ->
      failwith "cannot determine the type of some object, please help me"
  | RT s -> s
let to_effect (r,e) = Effect.from_u_effect (List.map to_region r) e

let rec to_ty =
  let h = Ht.create 17 in
  fun t ->
    try Ht.find h t
    with Not_found ->
      let r =
        match Uf.desc t with
        | U ->
            failwith "cannot determine the type of some object, please help me"
        | Arrow (t1,t2,e,cap) ->
            Ty.caparrow (to_ty t1) (to_ty t2)
              (to_effect e) (List.map to_region cap)
        | Tuple tl -> Ty.tuple (List.map to_ty tl)
        | Const c -> Ty.const c
        | Ref (r,t) -> Ty.ref_ (to_region r) (to_ty t)
        | Map e -> Ty.map (to_effect e)
        | PureArr (t1,t2) -> Ty.parr (to_ty t1) (to_ty t2)
        | App (v,i) -> Ty.app v (List.map to_ty i) in
      Ht.add h t r;
      r

let base_pre_ty eff = parr (map eff) prop
let base_post_ty eff t = parr (map eff) (parr (map eff) (parr t prop))
let pretype a e = parr a (base_pre_ty e)
let posttype a b e = parr a (base_post_ty e b)
let prepost_type a b e = tuple [ pretype a e ; posttype a b e ]

let to_logic_type t =
  node_map ~rfun:Misc.id ~eff_fun:Misc.id ~f:(fun t ->
    match Uf.desc t with
    | Arrow (t1,t2,e,_) -> prepost_type t1 t2 e
    | _ -> t) t

let print = Print.ty
let print_region = Print.region
let region_list = Print.region_list
