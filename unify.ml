module Uf = Unionfind
type 'a ty' = 
  | Var of int
  | Const of Ty.const
  | Arrow of 'a * 'a
  
type ty = U of ty ty' Uf.t

let fresh d = U (Uf.fresh d)
let new_ty n = fresh (Var n)
let arrow t1 t2 = fresh (Arrow (t1,t2))
let const c = fresh (Const c)

let union a b = Uf.union (fun a b -> a) a b

exception CannotUnify

let rec unify (U a) (U b) =
  if Uf.equal a b then ();
  match Uf.desc a, Uf.desc b with
  | Var n1, Var n2 -> 
      if n1 < n2 then union a b else union b a
  | Var _, _ -> union a b
  | _, Var _ -> union b a
  | Const c1, Const c2 when c1 = c2 -> union a b
  | Arrow (ta1,ta2), Arrow (tb1,tb2) -> 
      union a b;
      unify ta1 tb1;
      unify ta2 tb2
  | _, _ -> raise CannotUnify
      

let rec refresh_ty ~old ~new_ x =
  let h = Hashtbl.create 5 in
  let rec aux' x =
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
        if t1 == t1' && t2 == t2' then x
        else Uf.fresh (Arrow (t1,t2))
  and aux (U x) = U (aux' x) in
  aux x

