module Uf = Unionfind

type ty = 
  | U
  | T of node Ty.t'
and node = ty Uf.t

let new_ty () = Uf.fresh U
let mkt t = Uf.fresh (T t)
let arrow t1 t2 = mkt (Ty.Arrow (t1,t2)) 
let tuple t1 t2 = mkt (Ty.Tuple (t1,t2)) 
let var s = mkt (Ty.Var s)

open Const
let const =
  let h = Hashtbl.create 5 in
  List.iter (fun c -> Hashtbl.add h c (mkt (Ty.Const c))) 
    [ TBool ; TInt ; TUnit ];
  fun c -> Hashtbl.find h c

let union = Uf.union (fun a b -> a)

open Format
let rec print_node fmt x = 
  match Uf.desc x with
  | U -> fprintf fmt "%d" (Uf.tag x)
  | T t -> Ty.print' print_node fmt t

exception CannotUnify

let rec unify a b =
  if Uf.equal a b then ();
  match Uf.desc a, Uf.desc b with
  | U, U -> union a b
  | U _, T _ -> union b a
  | T _, U _ -> union a b
  | T t1, T t2 ->
      begin match t1, t2 with
      | Ty.Var s1, Ty.Var s2 when s1 = s2 -> ()
      | Ty.Const c1, Ty.Const c2 when c1 = c2 -> ()
      | Ty.Arrow (ta1,ta2), Ty.Arrow (tb1,tb2)
      | Ty.Tuple (ta1,ta2), Ty.Tuple (tb1,tb2) -> 
          unify ta1 tb1;
          unify ta2 tb2
      | _, Ty.Const _ -> 
          printf "unify: %a and %a@." print_node a print_node b;
          raise CannotUnify
      | _ , _ -> raise CannotUnify
      end; 
      union a b
      
let equal a b = Uf.tag a = Uf.tag b

(*
let rec refresh_ty ~old ~new_ z =
  let h = Hashtbl.create 5 in
  let rec aux' x = 
    match x with
    | Ty.Var _ | Ty.Const _ -> x
    | Ty.Arrow (t1,t2) -> 
        let t1' = aux t1 and t2' = aux t2 in
        if t1 == t1' && t2 == t2' then x else Ty.Arrow (t1',t2')
    | Ty.Tuple (t1,t2) -> 
        let t1' = aux t1 and t2' = aux t2 in
        if t1 == t1' && t2 == t2' then x else Ty.Tuple (t1',t2')
  and aux x = 
    match Uf.desc x with
    | T t ->
        let t' = aux' t in
        if t == t' then x else mkt t'
    | U n when n > old ->
        begin try Hashtbl.find h x
        with Not_found ->
          let k = new_ty new_ in
          Hashtbl.add h x k; k
        end
    | U _ -> x
  in aux z
*)

module H = Hashtbl.Make (struct 
                           type t = node
                           let equal a b = Uf.tag a = Uf.tag b
                           let hash (x : t) : int = Hashtbl.hash (Uf.tag x)
                         end)
