open Varsigs

module VarBase = 
struct
  include Name
  type name = t
  type subst = (t * t) list
  type 'a bind = subst * t * 'a
  type 'a listbind = subst * t list * 'a

  let to_name x = x
  let new_from_name = new_name
  let from_name x = x

  let refresh' (y,t) x = if equal x y then t else x
  let refresh = List.fold_right refresh'
  let refresh_bind s (s',v,t) = List.append s s', v, t
  let refresh_listbind s (s',v,t) = List.append s s', v, t

  let deb_open (_,v,t) = v,t
  let deb_listopen (_,vl,t) = vl,t

  let open_with f nv (s,v,t) = 
    let t = f [v,nv] t in
    f s t

  let open_bind f ((_,v,_) as k) =
    let nv = new_name v in
    let t = open_with f nv k in
    nv, t

  let close_bind nv t = ([],nv,t)

  let list_open_with f nvl (s,vl,t) =
    let subst = List.combine vl nvl in
    let t = f subst t in
    f s t

  let open_listbind f ((_,vl,_) as k) =
    let nvl = List.map new_name vl in
    let t = list_open_with f nvl k in
    nvl,t

  let close_listbind nvl t = ([],nvl,t)
end

module TyVar = VarBase
module Var = VarBase
module EffVar = VarBase
module RVar = VarBase

type subst = VarBase.subst
type subst' = subst

(*
let lookup_var = Var.from_string "!"
let assign_var = Var.from_string ":="
let ref_var = Var.from_string "ref"
let for_var_to = Var.from_string "forto"
let for_var_downto = Var.from_string "fordownto"
let map_get_var = Var.from_string "__get"
let map_set_var = Var.from_string "__set"
let map_combine_var = Var.from_string "combine"
let map_restrict_var = Var.from_string "restrict"
let map_empty_var = Var.from_string "empty"
let set_add_var = Var.from_string "add"
let set_union_var = Var.from_string "union"
let set_empty_var = Var.from_string "sempty"
let domain_var = Var.from_string "domain"
let plus_var = Var.from_string "Zplus"
let minus_var = Var.from_string "Zminus"
let mult_var = Var.from_string "Zmult"
let le_var = Var.from_string "Zle"
let leb_var = Var.from_string "Zleb"
let eqz_var = Var.from_string "beq_z"
let lt_var = Var.from_string "Zlt"
let ltb_var = Var.from_string "Zltb"
let max_var = Var.from_string "Zmax"
let min_var = Var.from_string "Zmin"
let and_var = Var.from_string "/\\"
let impl_var = Var.from_string "->"
let eqvar = Var.from_string "="
let mk_tuple_var = Var.from_string ","
let fst_var = Var.from_string "fst"
let snd_var = Var.from_string "snd"
let neg_var = Var.from_string "~"
*)
