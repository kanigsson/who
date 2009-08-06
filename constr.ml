open Vars

type t = 
  | True
  | Sub of Var.t * Ty.t
  | Eq of Ty.t * Ty.t
  | And of t * t
  | Exists of t TyVar.listbind
  | Let of constr_scheme * t Var.bind
and constr_scheme = (Ty.t * t) TyVar.listbind

open Format

let map ~varfun ~tyvarfun ~exbindfun ~letbindfun ~varbindfun t =
  let rec aux = function
  | True -> True
  | Sub (v,t) -> Sub (varfun v, Ty.map ~tyvarfun t)
  | Eq (t1,t2) -> Eq (Ty.map ~tyvarfun t1, Ty.map ~tyvarfun t2)
  | And (c1,c2) -> And (aux c1, aux c2)
  | Exists b -> Exists (exbindfun b)
  | Let (s, b) -> Let (letbindfun s, varbindfun b) in
  aux t

let refresh s t = 
  map ~varfun:(fun x -> Var.refresh s x) 
      ~tyvarfun:(fun x -> `Var (TyVar.refresh s x))
      ~exbindfun:(TyVar.refresh_listbind s)
      ~letbindfun:(TyVar.refresh_listbind s)
      ~varbindfun:(Var.refresh_bind s)
      t

let open_bind = Var.open_bind refresh
let open_tybind = TyVar.open_listbind refresh
let close_bind = Var.close_bind
let close_tybind = TyVar.close_listbind

let open_scheme = 
  TyVar.open_listbind (fun s (t,c) -> Ty.refresh s t, refresh s c)

let close_scheme = TyVar.close_listbind

let rec print fmt = function
  | True -> pp_print_string fmt "True"
  | Sub (v,t) -> fprintf fmt "%a < %a" Var.print v Ty.print t
  | And (c1,c2) -> fprintf fmt "%a /\ %a" print c1 print c2
  | Eq (t1,t2) -> fprintf fmt "%a = %a" Ty.print t1 Ty.print t2
  | Exists b ->
      let l,c = open_tybind b in
      fprintf fmt "∃%a.%a" TyVar.print_list l print c
  | Let (s,b) ->
      let v,c = open_bind b in
      fprintf fmt "let@ %a :@ %a@ in@ %a" Var.print v scheme s print c
and scheme fmt b = 
  let l,(t,c) = open_scheme b in
  fprintf fmt "∀%a[%a].%a" TyVar.print_list l Ty.print t print c

let exists f = 
  let x = TyVar.new_anon () in
  Exists (close_tybind [x] (f (Ty.var x)))

let exists2 f = 
  let x = TyVar.new_anon () in
  let y = TyVar.new_anon () in
  Exists (close_tybind [x;y] (f (Ty.var x) (Ty.var y)))

let let_ s x f = 
  Let (s, close_bind x f)

let true_ = True

let triv_scheme t = 
  close_scheme [] (t,true_)

let mk_scheme f = 
  let a = TyVar.new_anon () in
  close_scheme [a] (f (Ty.var a))
