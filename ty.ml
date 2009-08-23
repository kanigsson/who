type ('a,'b,'c) t' = 
  | Var of Name.t
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c
  | PureArr of 'a * 'a
  | App of Name.t * ('a,'b,'c) Inst.t
  | Ref of 'b * 'a
  | Map of 'c
type t = C of (t,Name.t,NEffect.t) t'

open Myformat

let is_compound = function
  | Var _ | Const _ | Ref _ | Map _ -> false
  | Tuple _ | Arrow _ | PureArr _ | App _ -> true

let maycap pr fmt = function
  | [] -> ()
  | l -> print_list space pr fmt l
let print' pt pr pe is_c fmt = function
  | Var x -> Name.print fmt x
  | Arrow (t1,t2,eff) -> 
      let p1 = if is_c t1 then paren pt else pt in
      fprintf fmt "%a ->%a %a" p1 t1 pe eff pt t2
  | PureArr (t1,t2) -> 
      let p1 = if is_c t1 then paren pt else pt in
      fprintf fmt "%a ->@ %a" p1 t1 pt t2
  | Tuple (t1,t2) -> fprintf fmt "%a *@ %a" pt t1 pt t2
  | Const c -> Const.print_ty fmt c
  | Ref (r,t) -> fprintf fmt "ref(%a,%a)" pr r pt t
  | Map e -> fprintf fmt "map%a" pe e
  | App (v,i) -> fprintf fmt "%a%a" Name.print v (Inst.print pt pr pe) i


let rec print fmt (C x) = 
  print' print Name.print NEffect.print 
    (function C x -> is_compound x) fmt x

let print_list sep fmt t = print_list sep print fmt t

let var v = C (Var v)
let arrow t1 t2 eff = C (Arrow (t1,t2,eff))
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
  | C (PureArr _) -> NEffect.empty
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
        let t = aux t1 in
        let e = NEffect.clean e in
        tuple (parr t (parr (map e) (prop))) 
          (parr t (parr (map e) (parr (map e) (parr (aux t2) (prop)))))
    | Ref (x,t) -> ref_ x (aux t)
    | App (v,i) -> app v i 
  and aux (C x) = aux' x in
  aux t 

let build_tvar_map el effl =
  List.fold_left2 (fun acc k v -> Name.M.add k v acc) Name.M.empty el effl

let tlsubst xl tl target = 
  let map = build_tvar_map xl tl in
  let rec aux' = function
    | (Var y as t)-> 
        begin try let C t = Name.M.find y map in t
        with Not_found -> t end
    | (Const _ | Map _ ) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff) -> Arrow (aux t1, aux t2,eff) 
    | Ref (r,t) -> Ref (r, aux t)
    | App (v,i) -> App (v,Inst.map aux Misc.id Misc.id i) 
  and aux (C x) = C (aux' x) in
  aux target

let build_rvar_map el effl =
  List.fold_left2 (fun acc k v -> Name.M.add k v acc) Name.M.empty el effl

let rlsubst rvl rl target = 
  let map = build_rvar_map rvl rl in
  let rec aux' = function
    | (Var _ | Const _) as x -> x
    | Tuple (t1,t2) -> Tuple (aux t1, aux t2) 
    | PureArr (t1,t2) -> PureArr (aux t1, aux t2) 
    | Arrow (t1,t2,eff) -> 
        Arrow (aux t1, aux t2,effsubst eff) 
    | Ref (r,t) -> Ref (auxr r, aux t)
    | Map e -> Map (effsubst e)
    | App (v,i) -> App (v, Inst.map aux auxr effsubst i)
  and auxr r = try Name.M.find r map with Not_found -> r
  and effsubst e = NEffect.rmap auxr e
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
  and effsubst eff' = NEffect.lsubst evl effl eff' in
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

  let print fmt ((tl,rl,el) as g) = 
    if is_empty g then ()
    else fprintf fmt "[%a|%a|%a]" Name.print_list tl 
          Name.print_list rl Name.print_list el

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

end

let allsubst ((tvl,rvl,evl) : Generalize.t) (tl,rl,el) target = 
  elsubst evl el (rlsubst rvl rl (tlsubst tvl tl target))

let rec equal' t1 t2 = 
  match t1, t2 with
  | Var x1, Var x2 -> Name.equal x1 x2
  | Const x1, Const x2 -> x1 = x2
  | Tuple (ta1,ta2), Tuple (tb1,tb2)
  | PureArr (ta1,ta2), PureArr (tb1,tb2) -> 
      equal ta1 tb1 && equal ta2 tb2
  | Arrow (ta1,ta2,e1), Arrow (tb1,tb2,e2) -> 
      equal ta1 tb1 && equal ta2 tb2 && NEffect.equal e1 e2 
  | Ref (r1,t1), Ref (r2,t2) -> Name.equal r1 r2 && equal t1 t2
  | Map e1, Map e2 -> NEffect.equal e1 e2
  | App (v1,i1), App (v2,i2) -> 
      v1 = v2 && Inst.equal equal Name.equal (NEffect.equal) i1 i2

  | _ -> false
and equal (C a) (C b) = equal' a b

let forty = 
  let e = Name.from_string "e" in
  let eff = NEffect.esingleton e in
  ([],[],[e]),
   parr 
     (parr int (parr (map eff) prop))
     (parr int (parr int (arrow (arrow int unit eff) unit eff)))

let h = Hashtbl.create 17

let add_var s x = Hashtbl.add h s x
let get_predef_var s = 
  try Hashtbl.find h s
  with Not_found -> failwith ("predef_var: " ^ s)

let iter_vars f = Hashtbl.iter f h

(*
let map ~tyvarfun ~effectfun ~rvarfun t =
  let rec aux' = function
  | (Const _ as t) -> t
  | `Tuple (t1,t2) -> `Tuple (aux t1, aux t2)
  | `Arr (t1,t2) -> `Arr (aux t1, aux t2)
  | `Var v -> tyvarfun v
  | `App (v,tl) -> `App (v, List.map r tl)
*)
