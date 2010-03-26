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

(* TODO Hashconsing *)
(* TODO Map function *)
type t =
  | Const of Const.ty
  | Tuple of t list
  | Arrow of t * t * Effect.t * Name.t list
  | PureArr of t * t
  | App of Name.t * (t,Name.t,Effect.t) Inst.t
  | Ref of Name.t * t
  | Map of Effect.t

open Myformat

let is_compound = function
  | Const _ | Ref _ | Map _ | App _ -> false
  | Tuple _ | Arrow _ | PureArr _ -> true

let maycap pr fmt = function
  | [] -> ()
  | l -> fprintf fmt "|%a" (print_list space pr) l

let varprint kind fmt x =
  match kind with
  | `Who -> fprintf fmt "'%a" Name.print x
  | `Coq | `Pangoline -> Name.print fmt x

let rec gen_print ?(kind=`Who) fmt x =
  let pt = gen_print ~kind in
  let mayp fmt t = if is_compound t then paren pt fmt t else pt fmt t in
  match x with
  | Arrow (t1,t2,eff,cap) ->
      (* there are no impure arrow types in Coq or Pangoline, so simply print it
      as you wish *)
      fprintf fmt "%a ->{%a%a} %a" mayp t1
        Effect.print eff (maycap Name.print) cap pt t2
  | Map e -> fprintf fmt "<%a>" Effect.print e
  | PureArr (t1,t2) -> fprintf fmt "%a ->@ %a" mayp t1 pt t2
  | Tuple tl ->
      print_list (fun fmt () -> fprintf fmt " *@ ") mayp fmt tl
  | Const c -> Const.print_ty kind fmt c
  | Ref (r,t) ->
      (* in Who, this is a special type constructor, in Coq its a simple
      application, in Pangoline its a type instantiation *)
      begin match kind with
      | `Who -> fprintf fmt "ref(%a,%a)" Name.print r pt t
      | `Coq -> fprintf fmt "ref@ %a@ %a" mayp t Name.print r
      | `Pangoline -> fprintf fmt "%a ref" mayp t
      end
  | App (v,i) ->
      fprintf fmt "%a%a" Name.print v
        (Inst.print ~kind ~intype:true mayp Name.print Effect.print) i

let print fmt x = gen_print ~kind:`Who fmt x
let coq_print fmt x = gen_print ~kind:`Coq fmt x

let print_list sep fmt t = print_list sep print fmt t

let arrow t1 t2 eff = Arrow (t1,t2,eff,[])
let caparrow t1 t2 eff cap = Arrow (t1,t2,eff,cap)
let parr t1 t2 = PureArr (t1,t2)
let tuple tl = Tuple tl
let const c = Const c
let ref_ r t = Ref (r,t)
let map e = Map e
let app v i = App (v,i)
let var v = App (v,Inst.empty)

module PI = Predefty.Identifier

let prop = const (Const.TProp)
let bool () = var (Predefty.var PI.bool_id)
let unit () = var (Predefty.var PI.unit_id)
let region x = app (Predefty.var PI.region_id) ([x],[],[])
let int = const (Const.TInt)

let emptymap = map (Effect.empty)

let is_unit t =
  match t with
  | App (v,([],[],[])) -> Predefty.equal v PI.unit_id
  | _ -> false

let tuple_list t = 
  match t with
  | Tuple l -> l
  | _ -> invalid_arg "tuple_arity"

let tuple_arity t = List.length (tuple_list t)

let destr_pair t =
  match t with
  | Tuple [t1;t2] -> t1,t2
  | _ ->  invalid_arg "Ty.destr_pair"

let latent_effect = function
  | Arrow (_,_,e,_) -> e
  | PureArr _ -> Effect.empty
  | _ -> assert false

let split t =
  match t with
  | Arrow (t1,t2,_,_) -> t1, t2
  | PureArr (t1,t2) -> t1, t2
  | _ -> failwith "split"

let arg t = fst (split t)
let result t = snd (split t)
let domain = function
  | Map e -> e
  | _ -> assert false

let is_map = function
  | Map _ -> true
  | _ -> false

let is_ref = function
  | Ref _ -> true
  | _ -> false

let pretype a e = parr a (parr (map e) prop)
let posttype a b e = parr a (parr (map e) (parr (map e) (parr b prop)))
let prepost_type a b e = tuple [pretype a e ; posttype a b e ]

let to_logic_type t =
  let rec aux = function
    | (Const _ | Map _) as t -> t
    | Tuple tl -> tuple (List.map aux tl)
    | PureArr (t1,t2) -> parr (aux t1) (aux t2)
    | Arrow (t1,t2,e,_) -> prepost_type (aux t1) (aux t2) e
    | Ref (x,t) -> ref_ x (aux t)
    | App (v,i) -> app v i in
  aux t

let build_tvar_map el effl =
  try
  List.fold_left2 (fun acc k v -> Name.M.add k v acc) Name.M.empty el effl
  with Invalid_argument _ ->
    failwith (Myformat.sprintf
      "not the right number of type arguments: expecting %a but %a is
      given.@." Name.print_list el (print_list Myformat.comma) effl)

let tlsubst xl tl target =
  let map = build_tvar_map xl tl in
  let rec aux = function
    | App (y,([],[],[])) as t ->
        begin try Name.M.find y map with Not_found -> t end
    | (Const _ | Map _ ) as x -> x
    | Tuple tl -> Tuple (List.map aux tl)
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2)
    | Arrow (t1,t2,eff,cap) -> Arrow (aux t1, aux t2,eff, cap)
    | Ref (r,t) -> Ref (r, aux t)
    | App (v,i) -> App (v,Inst.map aux Misc.id Misc.id i) in
  aux target

let build_rvar_map el effl =
  try
    List.fold_left2 (fun acc k v -> Name.M.add k v acc) Name.M.empty el effl
  with Invalid_argument _ ->
    failwith (Myformat.sprintf
      "not the right number of region arguments: expecting %a but %a is
      given.@." Name.print_list el Name.print_list effl)

let rlsubst rvl rl target =
(*
  Myformat.printf "building type %a[%a |-> %a]@."
  print target Name.print_list rvl Name.print_list rl;
*)
  let map = build_rvar_map rvl rl in
  let rec aux = function
    | Const _ as x -> x
    | Tuple tl -> Tuple (List.map aux tl)
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2)
    | Arrow (t1,t2,eff, cap) ->
        Arrow (aux t1, aux t2,effsubst eff, List.map auxr cap)
    | Ref (r,t) -> Ref (auxr r, aux t)
    | Map e -> Map (effsubst e)
    | App (v,i) -> App (v, Inst.map aux auxr effsubst i)
  and auxr r = try Name.M.find r map with Not_found -> r
  and effsubst e = Effect.rmap auxr e in
  aux target

exception Found of Name.t
let rsubst rvl rl r =
  try List.iter2 (fun k v ->
    if Name.equal k r then raise (Found v) else ()) rvl rl;
    r
  with Found v -> v

let elsubst evl effl target =
  let rec aux = function
    | Const _ as x -> x
    | Tuple tl -> Tuple (List.map aux tl)
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2)
    | Arrow (t1,t2,eff',cap) -> Arrow (aux t1, aux t2,effsubst eff' ,cap)
    | Map eff' -> Map (effsubst eff')
    | Ref (r,t) -> Ref (r, aux t)
    | App (v,i) -> App (v, Inst.map aux Misc.id effsubst i)
  and effsubst eff' = Effect.lsubst evl effl eff' in
  aux target

module Generalize = struct
  (* order : ty,r,e *)
  type t = Name.t list * Name.t list * Name.t list
  type 'a bind = 'a Name.listbind Name.listbind Name.listbind

  let empty = [],[],[]
  let is_empty = function
    | [],[],[] -> true
    | _ -> false

  open Myformat

  let varlist = print_list space (varprint `Who)
  let print fmt ((tl,rl,el) as g) =
    if is_empty g then ()
    else fprintf fmt "[%a|%a|%a]" varlist tl
          Name.print_list rl varlist el

  let open_ r b =
    let tl,b = Name.open_listbind Name.refresh_listbind b in
    let rl,b = Name.open_listbind Name.refresh_listbind b in
    let el,a = Name.open_listbind r b in
    (tl,rl,el), a

  let sopen_ (_,tl,(_,rl,(_,el,t))) = (tl,rl,el),t

  let close (tl,rl,el) a =
    Name.close_listbind tl (Name.close_listbind rl (Name.close_listbind el a))

  let equal =
    let eq = ExtList.equal Name.equal in
    fun (tl1,rl1,el1) (tl2,rl2,el2) ->
      eq tl1 tl2 && eq rl1 rl2 && eq el1 el2

  let get_first = function
    | [],[],x::_ | [],x::_,_ | x::_,_,_ -> x
    | [],[],[] -> assert false

end
module G = Generalize

let allsubst ((tvl,rvl,evl) : Generalize.t) (tl,rl,el) target =
  elsubst evl el (rlsubst rvl rl (tlsubst tvl tl target))

let rec equal t1 t2 =
  match t1, t2 with
  | Const x1, Const x2 -> x1 = x2
  | PureArr (ta1,ta2), PureArr (tb1,tb2) ->
      equal ta1 tb1 && equal ta2 tb2
  | Tuple tl1, Tuple tl2 when List.length tl1 = List.length tl2 ->
      List.for_all2 equal tl1 tl2
  | Arrow (ta1,ta2,e1, cap1), Arrow (tb1,tb2,e2, cap2) ->
      equal ta1 tb1 && equal ta2 tb2 && Effect.equal e1 e2 &&
      ExtList.equal Name.equal cap1 cap2
  | Ref (r1,t1), Ref (r2,t2) -> Name.equal r1 r2 && equal t1 t2
  | Map e1, Map e2 -> Effect.equal e1 e2
  | App (v1,i1), App (v2,i2) ->
      v1 = v2 && Inst.equal equal Name.equal (Effect.equal) i1 i2
  | _ -> false

let forty () =
  let e = Name.from_string "e" in
  let eff = Effect.esingleton e in
  let unit = unit () in
  ([],[],[e]),
   parr
     (parr int (parr (map eff) prop))
     (parr int (parr int (arrow (arrow int unit eff) unit eff)))

exception Found of t option

let find_type_of_r name x =
(*   Myformat.printf "finding %a in %a@." Name.print name print x; *)
  let rec aux = function
    | Const _ | Map _ -> None
    | Ref (n,t) -> if Name.equal n name then Some t else aux t
    | Arrow (t1,t2,_,_) | PureArr (t1,t2) ->
        begin match aux t1 with
        | (Some _) as r -> r
        | None -> aux t2
        end
    | Tuple tl
    | App (_,(tl,_,_)) ->
        try List.iter
          (fun t ->
            match aux t with
            | (Some _) as r -> raise (Found r)
            | None -> ()
          ) tl; None
        with Found t -> t in
  aux x

let get_reg = function
  | Ref (reg,_) -> reg
  | _ -> assert false

let selim_map get_rtype t =
  let rec aux = function
    | Const _ as t -> t
    | Map _ -> assert false
    | Tuple tl -> tuple (List.map aux tl)
    | PureArr (Map e, t) ->
        let t = Effect.efold (fun e acc -> parr (get_rtype e) acc) (aux t) e in
        Effect.rfold (fun r acc -> parr (get_rtype r) acc) t e
    | PureArr (t1,t2) -> parr (aux t1) (aux t2)
    | Arrow (t1,t2,e,cap) -> caparrow (aux t1) (aux t2) e cap
    | Ref (r,t) -> ref_ r (aux t)
    | App (v,i) -> app v (Inst.map aux Misc.id Misc.id i) in
(*   Myformat.printf "converting type: %a@." print t; *)
  aux t

let from_logic_pair t =
  match t with
  | Tuple [_;PureArr (t1,PureArr (Map e, PureArr (_, PureArr (t2, _))))] ->
      t1, t2, e
  | _ -> assert false
