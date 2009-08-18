open Vars
type ('a,'b,'c) t' = 
  | Var of tvar
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c
  | PureArr of 'a * 'a
  | App of tvar * ('a,'b,'c) Inst.t
  | Ref of 'b * 'a
  | Map of 'c
type t = C of (t,rvar,Effect.t) t'

open Myformat

let is_compound = function
  | Var _ | Const _ | Ref _ | Map _ -> false
  | Tuple _ | Arrow _ | PureArr _ | App _ -> true

let maycap pr fmt = function
  | [] -> ()
  | l -> print_list space pr fmt l
let print' pt pr pe is_c fmt = function
  | Var x -> pp_print_string fmt x
  | Arrow (t1,t2,eff) -> 
      let p1 = if is_c t1 then paren pt else pt in
      fprintf fmt "%a ->%a %a" p1 t1 pe eff pt t2
  | PureArr (t1,t2) -> 
      let p1 = if is_c t1 then paren pt else pt in
      fprintf fmt "%a ->@ %a" p1 t1 pt t2
  | Tuple (t1,t2) -> fprintf fmt "(%a *@ %a)" pt t1 pt t2
  | Const c -> Const.print_ty fmt c
  | Ref (r,t) -> fprintf fmt "ref(%a,%a)" pr r pt t
  | Map e -> fprintf fmt "map%a" pe e
  | App (v,i) -> fprintf fmt "%a%a" tvar v (Inst.print pt pr pe) i


let rec print fmt (C x) = 
  print' print pp_print_string Effect.print 
    (function C x -> is_compound x) fmt x

let print_list sep fmt t = print_list sep print fmt t

let var v = C (Var v)
let arrow t1 t2 eff = C (Arrow (t1,t2,eff))
let caparrow t1 t2 eff c = C (Arrow (t1,t2,eff))
let parr t1 t2 = C (PureArr (t1,t2))
let tuple t1 t2 = C (Tuple (t1,t2))
let const c = C (Const c)
let ref_ r t = C (Ref (r,t))
let map e = C (Map e)
let app v i = C (App (v,i))

let unit = const (Const.TUnit)
let prop = const (Const.TProp)
let bool = const (Const.TBool)
let int = const (Const.TInt)

let arg = function
  | C (Arrow (t1,_,_)) -> t1
  | C (PureArr (t1,_)) -> t1
  | _ -> assert false

let latent_effect = function
  | C (Arrow (_,_,e)) -> e
  | C (PureArr _) -> Effect.empty
  | _ -> assert false

let result = function
  | C (Arrow (_,t2,_)) -> t2
  | C (PureArr (_,t2)) -> t2
  | _ -> assert false

let to_logic_type t = 
  let rec aux' = function
    | (Var _ | Const _ | Map _) as t -> C t
    | Tuple (t1,t2) -> tuple (aux t1) (aux t2)
    | PureArr (t1,t2) -> parr (aux t1) (aux t2)
    | Arrow (t1,t2,e) -> 
        tuple (parr t1 (parr (map e) (prop))) 
          (parr t1 (parr (map e) (parr (map e) (parr t2 (prop)))))
    | Ref (x,t) -> ref_ x t
    | App (v,i) -> app v i 
  and aux (C x) = aux' x in
  aux t

module SM = Misc.StringMap
let tlsubst xl tl target = 
  let map = Misc.build_string_map xl tl in
  let rec aux' = function
    | (Var y as t)-> 
        begin try let C t = SM.find y map in t
        with Not_found -> t end
    | (Const _ | Map _ ) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff) -> Arrow (aux t1, aux t2,eff) 
    | Ref (r,t) -> Ref (r, aux t)
    | App (v,i) -> App (v,Inst.map aux Misc.id Misc.id i) 
  and aux (C x) = C (aux' x) in
  aux target

let rlsubst rvl rl target = 
  let map = Misc.build_string_map rvl rl in
  let rec aux' = function
    | (Var _ | Const _) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff) -> 
        Arrow (aux t1, aux t2,effsubst eff) 
    | Ref (r,t) -> Ref (auxr r, aux t)
    | Map e -> Map (effsubst e)
    | App (v,i) -> App (v, Inst.map aux auxr effsubst i)
  and auxr r = try SM.find r map with Not_found -> r
  and effsubst e = Effect.rmap auxr e
  and aux (C x) = C (aux' x) in
  aux target

let elsubst evl effl target = 
  let rec aux' = function
    | (Var _ | Const _ ) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff') -> Arrow (aux t1, aux t2,effsubst eff') 
    | Map eff' -> Map (effsubst eff')
    | Ref (r,t) -> Ref (r, aux t)
    | App (v,i) -> App (v, Inst.map aux Misc.id effsubst i)
  and aux (C x) = C (aux' x) 
  and effsubst eff' = Effect.lsubst evl effl eff' in
  aux target

module Generalize = struct
  type ty = t
  type t = tvar list * rvar list * effvar list

  let empty = [],[],[]
  let is_empty = function
    | [],[],[] -> true
    | _ -> false

  open Myformat
  let print fmt ((tl,rl,el) as g) = 
    if is_empty g then ()
    else fprintf fmt "[%a|%a|%a]" tvarlist tl rvarlist rl effvarlist el
end

let allsubst ((tvl,rvl,evl) : Generalize.t) (tl,rl,el) target = 
  elsubst evl el (rlsubst rvl rl (tlsubst tvl tl target))

let rec equal' t1 t2 = 
  match t1, t2 with
  | Var x1, Var x2 -> x1 = x2
  | Const x1, Const x2 -> x1 = x2
  | Tuple (ta1,ta2), Tuple (tb1,tb2)
  | PureArr (ta1,ta2), PureArr (tb1,tb2) -> 
      equal ta1 tb1 && equal ta2 tb2
  | Arrow (ta1,ta2,e1), Arrow (tb1,tb2,e2) -> 
      equal ta1 tb1 && equal ta2 tb2 && Effect.equal e1 e2 
  | Ref (r1,t1), Ref (r2,t2) -> r1 = r2 && equal t1 t2
  | Map e1, Map e2 -> Effect.equal e1 e2
  | App (v1,i1), App (v2,i2) -> 
      v1 = v2 && Inst.equal equal (=) (Effect.equal) i1 i2

  | _ -> false
and equal (C a) (C b) = equal' a b

let forty = 
  let e = "e" in
  let eff = Effect.esingleton e in
  ([],[],[e]),
   parr 
     (parr int (parr (map eff) prop))
     (parr int (parr int (arrow (arrow int unit eff) unit eff)))
