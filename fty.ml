open Vars

type ('a,'b,'c) t'' = [ ('a,'b) Lty.t'' | `Map of 'c ]
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

let map' r ~tyvarfun ~effectfun = function
  | #Lty.t' as t -> Lty.map' r ~tyvarfun t
  | `Map e -> `Map (effectfun e)

let map ~tyvarfun ~effectfun t = 
  let rec aux (`U t) = `U (map' aux ~tyvarfun ~effectfun t) in
  aux t

let refresh s t = 
  map ~tyvarfun:(fun v -> `Var (TyVar.refresh s v)) 
      ~effectfun:(Effect.refresh s) t

let effsubst ev eff t = 
  map ~tyvarfun:(fun v -> `Var v)
      ~effectfun:(Effect.effsubst ev eff) t

let tysubst tv (`U t) ft = 
  map ~tyvarfun:(fun v -> if TyVar.equal v tv then t else `Var v)
      ~effectfun:Misc.id ft

let leffsubst = List.fold_right2 effsubst
let ltysubst = List.fold_right2 tysubst

let rsubst r nr t = 
  map ~tyvarfun:(fun v -> `Var v)
      ~effectfun:(Effect.rsubst r nr) t

let lrsubst = List.fold_right2 rsubst

open Myformat
let print'' pra prb prc fmt = function
  | #Lty.t'' as t -> Lty.print'' pra prb fmt t
  | `Map e -> fprintf fmt "map%a" prc e

let print' pra fmt x = print'' pra TyVar.print Effect.print fmt x
let rec print fmt (`U t) = print' print fmt t

let print_list = print_list comma print
  
module Generalize = 
struct

  type 'a t = EffVar.t list * TyVar.t list * (RVar.t * 'a) list

  type ('a,'b) bind = ('a RVar.listbind * 'b list) TyVar.listbind EffVar.listbind 

  let refresh_r brefresh s (rl, bl) = 
    (RVar.refresh_listbind s rl, List.map (brefresh s) bl)

  let open_bind arefresh brefresh b = 
    let el, b = EffVar.open_listbind TyVar.refresh_listbind b in
    let tl, (b,rtl) = TyVar.open_listbind (refresh_r brefresh) b in
    let rl, c = RVar.open_listbind arefresh b in
    (el,tl,List.combine rl rtl), c

  let open_bind_with arefresh brefresh (el,tl,rl) c =
    let b = EffVar.list_open_with TyVar.refresh_listbind el c in
    let b,_ = TyVar.list_open_with (refresh_r brefresh) tl b in
    RVar.list_open_with arefresh (List.map fst rl) b

  let close_bind (el,tl, rl) c = 
    let rl, rtl = List.split rl in
    EffVar.close_listbind el 
      (TyVar.close_listbind tl 
        (RVar.close_listbind rl c, rtl))


  let is_empty (el,tl,rl) = el = [] && tl = [] && rl = []
  let empty = [],[],[]

  open Myformat
  let region ty fmt (r,a) = 
    fprintf fmt "%a : %a" RVar.print r ty a

  let region_list ty fmt l = print_list space (region ty) fmt l

  let print ty fmt (e,t,r) = 
    fprintf fmt "[%a|%a|%a]" EffVar.print_list e 
      TyVar.print_list t (region_list ty) r

end
module Scheme = 
struct
  type fty = t
  type t = (fty, fty) Generalize.bind

  let open_ x = Generalize.open_bind refresh refresh x
  let close = Generalize.close_bind

  let fty ft = close ([], [], []) ft

  let instance ts effl tyl nrl = 
    let (el,tl,rl),t = open_ ts in
    lrsubst (List.map fst rl) nrl (ltysubst tl tyl (leffsubst el effl t))

  let print fmt s = 
    let g, t = open_ s in
    Format.fprintf fmt "%a.%a" (Generalize.print print) g print t 

end

let compare' cmp a b = 
  match a,b with
  | (#Lty.t' as t1), (#Lty.t' as t2) -> Lty.compare' cmp t1 t2 
  | `Map e1, `Map e2 -> Effect.compare e1 e2
  | `Map _, _ -> 1
  | _, `Map _ -> -1
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
  | `U `Map _ -> Lty.var map_var in
  aux x

let ltyf t = lty (to_lty t)
