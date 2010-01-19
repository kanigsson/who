module PT = Predefined.Ty

type ('a,'b,'c) t' = 
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c * 'b list
  | PureArr of 'a * 'a
  | App of Name.t * ('a,'b,'c) Inst.t
  | Ref of 'b * 'a
  | Map of 'c
type t = C of (t,Name.t,Effect.t) t'

open Myformat

let is_compound = function
  | Const _ | Ref _ | Map _ -> false
  | Tuple _ | Arrow _ | PureArr _ | App _ -> true

let maycap pr fmt = function
  | [] -> ()
  | l -> fprintf fmt "|%a" (print_list space pr) l

let varprint kind fmt x = 
  match kind with
  | `Who -> fprintf fmt "'%a" Name.print x
  | `Coq | `Pangoline -> Name.print fmt x
  
let print' ?(kind=`Who) pt pr pe is_c fmt x = 
  let mayp fmt t = if is_c t then paren pt fmt t else pt fmt t in
  match x with 
  | Arrow (t1,t2,eff,cap) -> 
      (* there are no impure arrow types in Coq or Pangoline, so simply print it
      as you wish *)
      fprintf fmt "%a ->{%a%a} %a" mayp t1 pe eff (maycap pr) cap pt t2
  | Map e -> fprintf fmt "<%a>" pe e
  | PureArr (t1,t2) -> fprintf fmt "%a ->@ %a" mayp t1 pt t2
  | Tuple (t1,t2) -> fprintf fmt "%a *@ %a" mayp t1 mayp t2
  | Const c -> Const.print_ty fmt c
  | Ref (r,t) -> 
      (* in Who, this is a special type constructor, in Coq its a simple
      application, in Pangoline its a type instantiation *)
      begin match kind with
      | `Who -> fprintf fmt "ref(%a,%a)" pr r pt t
      | `Coq -> fprintf fmt "ref@ %a@ %a" mayp t pr r
      | `Pangoline -> fprintf fmt "%a ref@" mayp t
      end
  | App (v,i) -> 
      fprintf fmt "%a%a" Name.print v 
        (Inst.print ~kind ~intype:true mayp pr pe) i

let rec gen_print kind fmt (C x) = 
  print' ~kind (gen_print kind) Name.print Effect.print_nosep
    (function C x -> is_compound x) fmt x

let print fmt x = gen_print `Who fmt x

let coq_print fmt x = gen_print `Coq fmt x

let print_list sep fmt t = 
  print_list sep print fmt t

let arrow t1 t2 eff = C (Arrow (t1,t2,eff,[]))
let caparrow t1 t2 eff cap = C (Arrow (t1,t2,eff,cap))
let parr t1 t2 = C (PureArr (t1,t2))
let tuple t1 t2 = C (Tuple (t1,t2))
let const c = C (Const c)
let ref_ r t = C (Ref (r,t))
let map e = C (Map e)
let app v i = C (App (v,i))
let var v = C (App (v,Inst.empty))

let unit = const (Const.TUnit)
let prop = const (Const.TProp)
let bool = var (PT.bool_var)
let int = const (Const.TInt)
let emptymap = map (Effect.empty)

let destr_tuple (C t) = 
  match t with
  | Tuple (t1,t2) -> t1,t2
  | _ ->  invalid_arg "Ty.destr_tuple"

let latent_effect = function
  | C (Arrow (_,_,e,_)) -> e
  | C (PureArr _) -> Effect.empty
  | _ -> assert false

let split t = 
  match t with
  | C (Arrow (t1,t2,_,_)) -> t1, t2
  | C (PureArr (t1,t2)) -> t1, t2
  | _ -> failwith "split"

let arg t = fst (split t)
let result t = snd (split t)
let domain = function
  | C (Map e) -> e
  | _ -> assert false

let is_map = function
  | C (Map _) -> true
  | _ -> false

let is_ref = function
  | C (Ref _) -> true
  | _ -> false

let pretype a e = parr a (parr (map e) prop)
let posttype a b e = parr a (parr (map e) (parr (map e) (parr b prop)))
let prepost_type a b e = tuple (pretype a e) (posttype a b e)

let to_logic_type t = 
  let rec aux' = function
    | (Const _ | Map _) as t -> C t
    | Tuple (t1,t2) -> tuple (aux t1) (aux t2)
    | PureArr (t1,t2) -> parr (aux t1) (aux t2)
    | Arrow (t1,t2,e,_) -> prepost_type (aux t1) (aux t2) e 
    | Ref (x,t) -> ref_ x (aux t)
    | App (v,i) -> app v i 
  and aux (C x) = aux' x in
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
  let rec aux' = function
    | App (y,([],[],[])) as t -> 
        begin try let C t = Name.M.find y map in t
        with Not_found -> t end
    | (Const _ | Map _ ) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff,cap) -> Arrow (aux t1, aux t2,eff, cap) 
    | Ref (r,t) -> Ref (r, aux t)
    | App (v,i) -> App (v,Inst.map aux Misc.id Misc.id i) 
  and aux (C x) = C (aux' x) in
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
  let rec aux' = function
    | Const _ as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff, cap) -> 
        Arrow (aux t1, aux t2,effsubst eff, List.map auxr cap) 
    | Ref (r,t) -> Ref (auxr r, aux t)
    | Map e -> Map (effsubst e)
    | App (v,i) -> App (v, Inst.map aux auxr effsubst i)
  and auxr r = try Name.M.find r map with Not_found -> r
  and effsubst e = Effect.rmap auxr e
  and aux (C x) = C (aux' x) in
  aux target

exception Found of Name.t
let rsubst rvl rl r = 
  try List.iter2 (fun k v -> 
    if Name.equal k r then raise (Found v) else ()) rvl rl;
    r
  with Found v -> v

let elsubst evl effl target = 
  let rec aux' = function
    | Const _ as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff',cap) -> Arrow (aux t1, aux t2,effsubst eff' ,cap) 
    | Map eff' -> Map (effsubst eff')
    | Ref (r,t) -> Ref (r, aux t)
    | App (v,i) -> App (v, Inst.map aux Misc.id effsubst i)
  and aux (C x) = C (aux' x) 
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
    let eq = Misc.list_equal Name.compare in
    fun (tl1,rl1,el1) (tl2,rl2,el2) ->
      eq tl1 tl2 && eq rl1 rl2 && eq el1 el2

  let get_first = function
    | [],[],x::_ | [],x::_,_ | x::_,_,_ -> x
    | [],[],[] -> assert false

end
module G = Generalize

let allsubst ((tvl,rvl,evl) : Generalize.t) (tl,rl,el) target = 
  elsubst evl el (rlsubst rvl rl (tlsubst tvl tl target))

let rec equal' eff t1 t2 = 
  match t1, t2 with
  | Const x1, Const x2 -> x1 = x2
  | Tuple (ta1,ta2), Tuple (tb1,tb2)
  | PureArr (ta1,ta2), PureArr (tb1,tb2) -> 
      equal eff ta1 tb1 && equal eff ta2 tb2
  | Arrow (ta1,ta2,e1, cap1), Arrow (tb1,tb2,e2, cap2) -> 
      equal eff ta1 tb1 && equal eff ta2 tb2 && eff e1 e2 &&
      Misc.list_equal Name.compare cap1 cap2
  | Ref (r1,t1), Ref (r2,t2) -> Name.equal r1 r2 && equal eff t1 t2
  | Map e1, Map e2 -> eff e1 e2
  | App (v1,i1), App (v2,i2) -> 
      v1 = v2 && Inst.equal (equal eff) Name.equal (Effect.equal) i1 i2
  | _ -> false
and equal eff (C a) (C b) = equal' eff a b

let equal = equal Effect.equal

let forty = 
  let e = Name.from_string "e" in
  let eff = Effect.esingleton e in
  ([],[],[e]),
   parr 
     (parr int (parr (map eff) prop))
     (parr int (parr int (arrow (arrow int unit eff) unit eff)))

exception Found of t option

let find_type_of_r name x = 
(*   Myformat.printf "finding %a in %a@." Name.print name print x; *)
  let rec aux' = function
    | Const _ | Map _ -> None
    | Ref (n,t) -> if Name.equal n name then Some t else aux t
    | Tuple (t1,t2) | Arrow (t1,t2,_,_) | PureArr (t1,t2) -> 
        begin match aux t1 with
        | (Some _) as r -> r
        | None -> aux t2
        end
    | App (_,(tl,_,_)) ->
        try List.iter
          (fun t -> 
            match aux t with
            | (Some _) as r -> raise (Found r)
            | None -> ()
          ) tl; None
        with Found t -> t
  and aux (C t) = aux' t in
  aux x

let get_reg = function
  | C (Ref (reg,_)) -> reg 
  | _ -> assert false

let selim_map get_rtype t = 
  let rec aux' = function
    | Const _ as t -> C t
    | Map _ -> assert false
    | Tuple (t1,t2) -> tuple (aux t1) (aux t2)
    | PureArr (C (Map e), t) ->
        let t = Effect.efold (fun e acc -> parr (get_rtype e) acc) (aux t) e in
        Effect.rfold (fun r acc -> parr (get_rtype r) acc) t e
    | PureArr (t1,t2) -> parr (aux t1) (aux t2)    
    | Arrow (t1,t2,e,cap) -> caparrow (aux t1) (aux t2) e cap
    | Ref (r,t) -> ref_ r (aux t)
    | App (v,i) -> app v (Inst.map aux Misc.id Misc.id i)
  and aux (C t) = aux' t in
(*   Myformat.printf "converting type: %a@." print t; *)
  aux t

let selim_map_log t = 
  let rec aux' = function
    | Const _ as t -> C t
    | Map _ -> assert false
    | Tuple (t1,t2) -> tuple (aux t1) (aux t2)
    | PureArr (t1,t2) -> parr (aux t1) (aux t2)    
    | Arrow (t1,t2,e,_) -> prepost_type (aux t1) (aux t2) e
    | Ref (r,t) -> ref_ r (aux t)
    | App (v,i) -> app v (Inst.map aux Misc.id Misc.id i)
  and aux (C t) = aux' t in
  aux t

module Predef = struct
  let prop_2 = parr prop prop
  let prop_3 = parr prop (parr prop prop)
  let bool_3 = parr bool (parr bool bool)
  let int_3 = parr int (parr int int)
  let iip = parr int (parr int prop)
  let iib = parr int (parr int bool)
  let aap, aab, mk_tuple, fst, snd = 
    let a = Name.from_string "a" and b = Name.from_string "b" in
    let ta = var a and tb = var b in
    (([a],[],[]), parr ta (parr ta prop)),
    (([a],[],[]), parr ta (parr ta bool)),
    (([a;b],[],[]), parr ta (parr tb (tuple ta tb))),
    (([a;b],[],[]), parr (tuple ta tb) ta),
    (([a;b],[],[]), parr (tuple ta tb) tb)

  let combine, restrict, get =
    let es = Effect.esingleton and nf = Name.from_string in
    let ess a b = Effect.eadd (es a) b in
    let e1 = nf "e1" and e2 = nf "e2" and e3 = nf "e3" in
    let a = Name.from_string "c" in
    let ta = var a in
    let r = Name.from_string "r" in
    let eff1 = ess e1 e2 and eff2 = ess e2 e3 in
    let eff3 = Effect.eadd eff1 e3 in
    (([],[],[e1;e2;e3]), parr (map eff1) (parr (map eff2) (map eff3))) ,
    (([],[],[e1;e2]), parr (map eff1) (map (es e2))), 
    (([a],[r],[e1]), parr (ref_ r ta) (parr (map (Effect.radd (es e1) r)) ta))

end
