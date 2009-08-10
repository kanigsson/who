module Uf = Unionfind
type ty' = 
  | Var of int
  | Const of Const.ty
  | Arrow of ty * ty
and ty = ty' Uf.t

let new_ty n = Uf.fresh (Var n)
let arrow t1 t2 = Uf.fresh (Arrow (t1,t2))
let const c = Uf.fresh (Const c)

let union = Uf.union (fun a b -> a)

open Format
let rec print_node fmt x = 
  match Uf.desc x with
  | Var n -> fprintf fmt "%d:%d" (Uf.tag x) n
  | Arrow (t1,t2) -> fprintf fmt "(%a -> %a)" print_node t1 print_node t2
  | Const c -> Const.print_ty fmt c

exception CannotUnify

let rec unify a b =
  if Uf.equal a b then ();
  match Uf.desc a, Uf.desc b with
  | Var n1, Var n2 -> 
      if n1 < n2 then union a b else union b a
  | Var _, _ -> union b a
  | _, Var _ -> union a b
  | Const c1, Const c2 when c1 = c2 -> union a b
  | Arrow (ta1,ta2), Arrow (tb1,tb2) -> 
      union a b;
      unify ta1 tb1;
      unify ta2 tb2
  | _, _ -> raise CannotUnify
      
let equal a b = Uf.tag a = Uf.tag b

let rec refresh_ty ~old ~new_ z =
  let h = Hashtbl.create 5 in
  let rec aux x =
    match Uf.desc x with
    | Var n when n > old -> 
        begin try Hashtbl.find h x
        with Not_found ->
          let k = Uf.fresh (Var new_) in
          Hashtbl.add h x k; k
        end
    | Var _ -> x
    | (Const _) -> x
    | Arrow (t1,t2) -> 
        let t1' = aux t1 and t2' = aux t2 in
        if t1 == t1' && t2 == t2' then x else Uf.fresh (Arrow (t1',t2')) in
  aux z

module H = Hashtbl.Make (struct 
                           type t = ty
                           let equal a b = Uf.tag a = Uf.tag b
                           let hash (x : t) : int = Hashtbl.hash (Uf.tag x)
                         end)

