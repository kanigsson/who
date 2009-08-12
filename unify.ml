module Uf = Unionfind

type ty = 
  | U
  | T of (node,rnode) Ty.t'
and node = ty Uf.t
and rnode = r Uf.t
and r = 
  | RU 
  | RT of string

let new_ty () = Uf.fresh U
let mkt t = Uf.fresh (T t)
let arrow t1 t2 = mkt (Ty.Arrow (t1,t2)) 
let tuple t1 t2 = mkt (Ty.Tuple (t1,t2)) 
let ref_ r t = mkt (Ty.Ref (r, t))
let mkr r = Uf.fresh (RT r)
let new_r () = Uf.fresh RU
let var s = mkt (Ty.Var s)

open Const
let const =
  let h = Hashtbl.create 5 in
  List.iter (fun c -> Hashtbl.add h c (mkt (Ty.Const c))) 
    [ TBool ; TInt ; TUnit ];
  fun c -> Hashtbl.find h c

let union a b = Uf.union (fun a b -> a) a b

open Format
let rec print_node fmt x = 
  match Uf.desc x with
  | U -> fprintf fmt "%d" (Uf.tag x)
  | T t -> Ty.print' print_node prvar fmt t
and prvar fmt x = 
  match Uf.desc x with
  | RU -> fprintf fmt "%d" (Uf.tag x)
  | RT s -> pp_print_string fmt s


exception CannotUnify

let rec unify a b =
  if Uf.equal a b then ();
  match Uf.desc a, Uf.desc b with
  | U, U -> union a b
  | U _, T _ -> union b a
  | T _, U _ -> union a b
  | T t1, T t2 ->
      union a b;
      begin match t1, t2 with
      | Ty.Var s1, Ty.Var s2 when s1 = s2 -> ()
      | Ty.Const c1, Ty.Const c2 when c1 = c2 -> ()
      | Ty.Arrow (ta1,ta2), Ty.Arrow (tb1,tb2)
      | Ty.Tuple (ta1,ta2), Ty.Tuple (tb1,tb2) -> 
          unify ta1 tb1;
          unify ta2 tb2
      | Ty.Ref (r1,t1), Ty.Ref (r2,t2) -> 
          runify r1 r2;
          unify t1 t2
      | _, Ty.Const _ -> 
          printf "unify: %a and %a@." print_node a print_node b;
          raise CannotUnify
      | _ , _ -> raise CannotUnify
      end; 
and runify a b = 
  if Uf.equal a b then ();
  match Uf.desc a, Uf.desc b with
  | RU, RU -> union a b
  | RU _, RT _ -> union b a
  | RT _, RU _ -> union a b
  | RT s1, RT s2 when s1 = s2 -> ()
  | RT _, RT _ -> raise CannotUnify
      
let equal a b = Uf.tag a = Uf.tag b

module H = Hashtbl.Make (struct 
                           type t = node
                           let equal a b = Uf.tag a = Uf.tag b
                           let hash (x : t) : int = Hashtbl.hash (Uf.tag x)
                         end)
let to_ty =
  let h = H.create 127 in
  let rec ty' = function
    | Ty.Var s -> Ty.var s
    | Ty.Arrow (t1,t2) -> Ty.arrow (ty t1) (ty t2)
    | Ty.Tuple (t1,t2) -> Ty.tuple (ty t1) (ty t2)
    | Ty.Const c -> Ty.const c
    | Ty.Ref (r,t) -> Ty.ref_ (rv r) (ty t)
  and ty x = 
    try H.find h x 
    with Not_found -> 
      match Unionfind.desc x with
      | U _ -> assert false
      | T t -> 
          let r = ty' t in
          H.add h x r; r
  and rv r = 
    match Uf.desc r with
    | RU -> assert false
    | RT t -> t in
  ty

