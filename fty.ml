open Vars

type ('a,'b,'c) t'' = [ ('a,'b) Lty.t'' | `Map of 'c | `Ref of RVar.t * 'a ]
type 'a t' = ('a,TyVar.t,Effect.t) t''
type t = [ `U of t t' ]

let lty' t = ( t : 'a Lty.t' :> 'a t')
let lty t = ( t : Lty.t :> t)
let const c = `U (`Const c)
let prop = lty (Lty.prop)
let int = lty (Lty.int)
let bool = lty (Lty.bool)
let unit = lty (Lty.unit)
let var v = `U (`Var v)

let key_var = TyVar.from_string "key"
let map_var = TyVar.from_string "kmap"
let set_var = TyVar.from_string "kset"

let app v t = `U (`App (v,t))
let arr t1 t2 = `U (`Arr (t1,t2))
let tuple t1 t2 = `U (`Tuple (t1,t2))
let app t1 l = `U (`App (t1,l))
let mkmap eff = `U (`Map eff)
let maparr eff t = arr (mkmap eff) t
let massarrow tl t = List.fold_right (fun x acc -> arr x acc) tl t

let iii = arr int (arr int int)
let iip = arr int (arr int prop)
let iib = arr int (arr int bool)
let ppp = arr prop (arr prop prop)

let mmm,smm,kss,sss,ms,kvmm = 
  let m = var map_var in
  let s = var set_var in
  let k = var key_var in
  arr m (arr m m), 
  arr s (arr m m),
  arr k (arr s s),
  arr s (arr s s),
  arr m s,
  (fun t -> arr k (arr t (arr m m)))

let lift f x = lty (f x)
let lift' f x = lty' (f x)

let var = lift Lty.var

let map' r ~tyvarfun ~effectfun ~rvarfun = function
  | #Lty.t' as t -> Lty.map' r ~tyvarfun t
  | `Map e -> `Map (effectfun e)
  | `Ref (rv,e) -> `Ref (rvarfun rv, r e)

let map ~tyvarfun ~effectfun ~rvarfun t = 
  let rec aux (`U t) = `U (map' aux ~tyvarfun ~effectfun ~rvarfun t) in
  aux t

let refresh s t = 
  map ~tyvarfun:(fun v -> `Var (TyVar.refresh s v)) 
      ~effectfun:(Effect.refresh s) 
      ~rvarfun:(RVar.refresh s) 
      t

let effsubst ev eff t = 
  map ~tyvarfun:(fun v -> `Var v)
      ~effectfun:(Effect.effsubst ev eff) ~rvarfun:Misc.id t

let tysubst tv (`U t) ft = 
  map ~tyvarfun:(fun v -> if TyVar.equal v tv then t else `Var v)
      ~effectfun:Misc.id ~rvarfun:Misc.id ft

let leffsubst = List.fold_right2 effsubst
let ltysubst = List.fold_right2 tysubst

let rsubst r nr t = 
  map ~tyvarfun:(fun v -> `Var v)
      ~effectfun:(Effect.rsubst r nr) 
      ~rvarfun:(fun v -> if RVar.equal v r then nr else v)
        t

let lrsubst = List.fold_right2 rsubst

open Myformat
let print'' pra prb prc fmt = function
  | #Lty.t'' as t -> Lty.print'' pra prb fmt t
  | `Map e -> fprintf fmt "map%a" prc e
  | `Ref (r,t) -> fprintf fmt "ref(%a,%a)" RVar.print r pra t

let print' pra fmt x = print'' pra TyVar.print Effect.print fmt x
let rec print fmt (`U t) = print' print fmt t

let print_list = print_list comma print
  
module Generalize = 
struct

  type t =  TyVar.t list * RVar.t list * EffVar.t list

  type 'a bind = 'a RVar.listbind TyVar.listbind EffVar.listbind 

  let refresh_r brefresh s (rl, bl) = 
    (RVar.refresh_listbind s rl, List.map (brefresh s) bl)

  let open_bind r b = 
    let el, b = EffVar.open_listbind TyVar.refresh_listbind b in
    let tl, b = TyVar.open_listbind RVar.refresh_listbind b in
    let rl, c = RVar.open_listbind r b in
    (tl,rl,el), c

  let open_bind_with arefresh (tl,rl,el) c =
    let b = EffVar.list_open_with TyVar.refresh_listbind el c in
    let b = TyVar.list_open_with (RVar.refresh_listbind) tl b in
    RVar.list_open_with arefresh rl b

  let close_bind (tl, rl, el) c = 
    EffVar.close_listbind el 
      (TyVar.close_listbind tl (RVar.close_listbind rl c))


  let is_empty (tl,rl,el) = el = [] && tl = [] && rl = []
  let empty = [],[],[]

  open Myformat
  let print fmt (t,r,e) = 
    fprintf fmt "[%a|%a|%a]" TyVar.print_list t RVar.print_list r 
      EffVar.print_list e 
      
  let from_g (tl,rl,el) =
    List.map EffVar.from_name el,
    List.map TyVar.from_name tl, 
    List.map RVar.from_name rl

end
module Scheme = 
struct
  type fty = t
  type t = fty Generalize.bind

  let open_ x = Generalize.open_bind refresh x
  let close = Generalize.close_bind

  let fty ft = close ([], [], []) ft

  let instance ts effl tyl nrl = 
    let (tl,rl,el),t = open_ ts in
    lrsubst rl nrl (ltysubst tl tyl (leffsubst el effl t))

  let print fmt s = 
    let g, t = open_ s in
    Format.fprintf fmt "%a.%a" Generalize.print g print t 

end

let compare' cmp a b = 
  match a,b with
  | (#Lty.t' as t1), (#Lty.t' as t2) -> Lty.compare' cmp t1 t2 
  | `Map e1, `Map e2 -> Effect.compare e1 e2
  | `Map _, _ -> 1
  | _, `Map _ -> -1
  | `Ref (r1,t1), `Ref (r2,t2) -> 
      let c = RVar.compare r1 r2 in
      if c = 0 then cmp t1 t2 else c
  | `Ref _, _ -> 1
  | _, `Ref _ -> -1
let rec compare (`U a) (`U b) = compare' compare a b

let equal a b = compare a b = 0

open Vars

let binder fmt (v,t) = 
  match t with
  | `U `Const Const.TUnit -> pp_print_string fmt "()"
  | _ -> fprintf fmt "@[%a@ :@ %a@]" Var.print v print t

let arr t1 t2 = `U (`Arr (t1,t2))
let tuple t1 t2 = `U (`Tuple (t1,t2))
let app t1 l = `U (`App (t1,l))
let mkmap eff = `U (`Map eff)
let maparr eff t = arr (mkmap eff) t

let well_formed' wf arity x =
  match x with
  | #Lty.t' as t -> Lty.well_formed' wf arity t
  | `Map _ -> true
  | `Ref (_,t) -> wf t
let well_formed arity t = 
  let rec aux (`U t) = well_formed' aux arity t in 
  aux t

let domain = function
  | `U `Map e -> e
  | _ -> assert false

let arg = function
  | `U `Arr (t1,_) -> t1
  | _ -> assert false

let result = function
  | `U `Arr (_,t2) -> t2
  | _ -> assert false

let left = function
  | `U `Tuple (a,_) -> a
  | _ -> assert false

let right = function
  | `U `Tuple (_,b) -> b
  | _ -> assert false

let to_lty x = 
  let rec aux = function
  | `U `Var v -> Lty.var v
  | `U `Const c -> Lty.const c
  | `U `Tuple (t1,t2) -> Lty.tuple (aux t1) (aux t2)
  | `U `Arr (t1,t2) -> Lty.arr (aux t1) (aux t2)
  | `U `App (v,tl) -> Lty.app v (List.map aux tl)
  | `U `Map _ -> Lty.var map_var
  | `U `Ref _ -> assert false in
  aux x

let ltyf t = lty (to_lty t)

let from_ty, from_eff = 
  let rec aux' = function
    | Ty.Var n -> `Var (tvar n)
    | Ty.Const c -> `Const c
    | Ty.Tuple (t1,t2) -> `Tuple (aux t1, aux t2)
    | Ty.PureArr (t1, t2) -> `Arr (aux t1, aux t2)
    | Ty.Arrow _ -> assert false
    | Ty.App (n, (tl,_,_)) -> `App (tvar n, List.map aux tl)
    | Ty.Ref (r,t) -> `Ref (RVar.from_name r, aux t)
    | Ty.Map e -> `Map (eff e)
  and aux (Ty.C t) = `U (aux' t) 
  and eff (rl,el,_) = 
    Name.S.fold
      (fun r acc -> Effect.radd (rvar r) acc) rl
      (Name.S.fold
        (fun e acc -> Effect.eadd (EffVar.from_name e) acc)
        el Effect.empty)
  and rvar = RVar.from_name
  and tvar = TyVar.from_name in
  aux, eff

let h = Hashtbl.create 17

let init () = 
  Ty.iter_vars (fun k (v,(tl,_,_),t) -> 
    Hashtbl.add h k (Var.from_name v,List.map TyVar.from_name tl, from_ty t))
(*
  Hashtbl.iter
    (fun k (v,tl,t) ->
      Format.printf "%s : (%a,%a,%a)@." k Var.print v TyVar.print_list tl
      print t) h
*)

let get_predef_var x = Hashtbl.find h x

