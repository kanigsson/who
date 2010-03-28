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
let const c = Const c
let ref_ r t = Ref (r,t)
let map e = Map e
let app v i = App (v,i)
let var v = App (v,Inst.empty)
let ty_app v tl = app v (tl,[],[])

module PI = Predefty.Identifier

let prop = const (Const.TProp)
let bool () = var (Predefty.var PI.bool_id)
let unit () = var (Predefty.var PI.unit_id)
let region x = ty_app (Predefty.var PI.region_id) [x]
let refty x y = ty_app (Predefty.var PI.refty_id) [x;y]
let int = const (Const.TInt)

let tuple tl =
  match tl with
  | [] -> unit ()
  | [x] -> x
  | _ -> Tuple tl

let emptymap = map (Effect.empty)

let is_unit t =
  match t with
  | App (v,([],[],[])) -> Predefty.equal v PI.unit_id
  | _ -> false

let tuple_list t =
  match t with
  | Tuple l -> l
  | _ -> invalid_arg "tuple_list"

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
  | _ -> invalid_arg "split"

let pure_split t = 
  match t with
  | PureArr (t1,t2) -> t1, t2
  | _ -> invalid_arg "pure_split"

let nsplit t = 
  let rec aux acc t = 
    try  
      let t1,t2 = pure_split t in
      aux (t1::acc) t2
    with Invalid_argument _ -> acc, t
  in
  let tl, t = aux [] t in
  List.rev tl, t

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

let destr_ref = function
  | Ref (_,t) -> t
  | _ -> invalid_arg "destr_ref"

let pretype a e = parr a (parr (map e) prop)
let posttype a b e = parr a (parr (map e) (parr (map e) (parr b prop)))
let prepost_type a b e = tuple [pretype a e ; posttype a b e ]

let node_map ?(rfun=Misc.id) ?(effectfun=Misc.id) f t =
  let rec aux t =
    let t =
      match t with
      | (Const _ ) as t -> t
      | Map e -> Map (effectfun e)
      | Tuple tl -> tuple (List.map aux tl)
      | PureArr (t1,t2) -> parr (aux t1) (aux t2)
      | Arrow (t1,t2,e,rl) ->
          caparrow (aux t1) (aux t2) (effectfun e) (List.map rfun rl)
      | Ref (r,t) -> ref_ (rfun r) (aux t)
      | App (v,i) -> app v (Inst.map aux rfun effectfun i) in
    f t in
  aux t

let to_logic_type =
  let f t =
    match t with
    | Arrow (t1,t2,e,_) -> prepost_type t1 t2 e
    | _ -> t
  in
  node_map f

let build_var_map nl il =
  try
  List.fold_left2 (fun acc k v -> Name.M.add k v acc) Name.M.empty nl il
  with Invalid_argument _ -> invalid_arg "build_var_map"
(*
    failwith (Myformat.sprintf
      "not the right number of type arguments: expecting %a but %a is
      given.@." Name.print_list nl (print_list Myformat.comma) il)
*)

let tlsubst xl tl =
  let map = build_var_map xl tl in
  let f t = match t with
  | App (y,([],[],[])) as t ->
      begin try Name.M.find y map with Not_found -> t end
  | _ -> t in
  node_map f

let rlsubst rvl rl =
  let map = build_var_map rvl rl in
  let rfun r = try Name.M.find r map with Not_found -> r in
  let effectfun e = Effect.rmap rfun e in
  node_map ~rfun ~effectfun Misc.id

exception Found of Name.t
let rsubst rvl rl r =
  try List.iter2 (fun k v ->
    if Name.equal k r then raise (Found v) else ()) rvl rl;
    r
  with Found v -> v

let elsubst evl effl =
  let effectfun eff' = Effect.lsubst evl effl eff' in
  node_map ~effectfun Misc.id

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

type scheme = G.t * t

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

let selim_map get_rtype =
  let f t = match t with
  | PureArr (Map e, t) ->
      let t = Effect.efold (fun e acc -> parr (get_rtype e) acc) t e in
      Effect.rfold (fun r acc -> parr (get_rtype r) acc) t e
  | _ -> t
  in
  node_map f

let from_logic_pair t =
  match t with
  | Tuple [_;PureArr (t1,PureArr (Map e, PureArr (_, PureArr (t2, _))))] ->
      t1, t2, e
  | _ -> assert false

exception TypeMismatch

let matching vars =
  let rec matching s ty1 ty2 =
    match ty1, ty2 with
    | App (v,([],[],[])), _ when Name.S.mem v vars ->
        begin try if equal (Name.M.find v s) ty2 then s else raise TypeMismatch
        with Not_found -> Name.M.add v ty2 s end
    | Const c1, Const c2 when Const.equal_t c1 c2 -> s
    | Map e1, Map e2 when Effect.equal e1 e2 -> s
    | Tuple tl1, Tuple tl2 when List.length tl1 = List.length tl2 -> 
        List.fold_left2 matching s tl1 tl2
    | PureArr (ta1,ta2), PureArr (tb1,tb2) -> 
        let s = matching s ta1 tb1 in
        matching s ta2 tb2
    | Ref (r1,t1), Ref (r2,t2) when Name.equal r1 r2 -> matching s t1 t2
    | App (v1,i1), App (v2,i2) when Name.equal v1 v2 ->
        inst_matching s i1 i2
    | _ -> raise TypeMismatch
  and inst_matching s (tl1,rl1,el1) (tl2,rl2,el2) = 
    if ExtList.equal Name.equal rl1 rl2 && ExtList.equal Effect.equal el1 el2
      && List.length tl1 = List.length tl2 then
        List.fold_left2 matching s tl1 tl2
    else raise TypeMismatch
  in
  matching

