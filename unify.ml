module Uf = Unionfind
module SS = Misc.SS

type ty = 
  | U
  | T of (node,rnode, enode) Ty.t'
and node = ty Uf.t
and rnode = r Uf.t
and enode = e Uf.t
and r = 
  | RU 
  | RT of string
and e = 
  | EU
  | EV of string
  | ET of rnode list * enode list

let new_ty () = Uf.fresh U
let mkt t = Uf.fresh (T t)
let arrow t1 t2 e = mkt (Ty.Arrow (t1,t2,e)) 
let tuple t1 t2 = mkt (Ty.Tuple (t1,t2)) 
let ref_ r t = mkt (Ty.Ref (r, t))
let mkr r = Uf.fresh (RT r)
let new_r () = Uf.fresh RU
let var s = mkt (Ty.Var s)
let map e = mkt (Ty.Map e)
let parr t1 t2 = mkt (Ty.PureArr (t1,t2))

let new_e () = Uf.fresh EU
let mke e = Uf.fresh (EV e)

let effect rl el = Uf.fresh (ET (rl,el))

open Const
let const =
  let h = Hashtbl.create 5 in
  List.iter (fun c -> Hashtbl.add h c (mkt (Ty.Const c))) 
  [ TBool ; TInt ; TUnit; TProp ];
  fun c -> Hashtbl.find h c

let prop = const TProp

let union a b = Uf.union (fun a b -> a) a b
let eunion a b = 
  match a,b with
  | EU, EU -> a
  | EU, _ -> b
  | _, EU -> a
  | EV a, EV b -> ET ([],[mke a; mke b])
  | (EV a, ET (rl, el)) 
  | ET (rl,el), EV a -> ET (rl, (mke a)::el)
  | ET (rl1,el1), ET (rl2,el2) -> ET (rl1 @ rl2, el1 @ el2)

let eunion a b = Uf.union eunion a b

open Myformat
let rec print_node fmt x = 
  match Uf.desc x with
  | U -> fprintf fmt "%d" (Uf.tag x)
  | T t -> Ty.print' print_node prvar preff fmt t
and prvar fmt x = 
  match Uf.desc x with
  | RU -> fprintf fmt "%d" (Uf.tag x)
  | RT s -> pp_print_string fmt s
and preff fmt x = 
  match Uf.desc x with
  | EU -> fprintf fmt "%d" (Uf.tag x)
  | EV x -> pp_print_string fmt x
  | ET (rl,el) -> 
      let p r = print_list space r in
      fprintf fmt "{%a %a}" (p prvar) rl (p preff) el



exception CannotUnify

open Format
let rec unify a b =
  printf "unify: %a and %a@." print_node a print_node b;
  if Uf.equal a b then () else
  match Uf.desc a, Uf.desc b with
  | U, U -> union a b
  | U _, T _ -> union b a
  | T _, U _ -> union a b
  | T t1, T t2 ->
      union a b;
      begin match t1, t2 with
      | Ty.Var s1, Ty.Var s2 when s1 = s2 -> ()
      | Ty.Const c1, Ty.Const c2 when c1 = c2 -> ()
      | Ty.PureArr (ta1,ta2), Ty.PureArr (tb1,tb2)
      | Ty.Arrow (ta1,ta2,_), Ty.PureArr (tb1,tb2)
      | Ty.PureArr (ta1,ta2), Ty.Arrow (tb1,tb2,_)
      | Ty.Tuple (ta1,ta2), Ty.Tuple (tb1,tb2) -> 
          unify ta1 tb1;
          unify ta2 tb2
      | Ty.Arrow (ta1,ta2,e1), Ty.Arrow (tb1,tb2,e2) ->
          unify ta1 tb1;
          unify ta2 tb2;
          eunify e1 e2
      | Ty.Ref (r1,t1), Ty.Ref (r2,t2) -> 
          runify r1 r2;
          unify t1 t2
      | Ty.Map e1, Ty.Map e2 -> eunify e1 e2
      | _ , _ -> 
          raise CannotUnify
      end; 
and runify a b = 
  if Uf.equal a b then () else
  match Uf.desc a, Uf.desc b with
  | RU, RU -> union a b
  | RU _, RT _ -> union b a
  | RT _, RU _ -> union a b
  | RT s1, RT s2 when s1 = s2 -> ()
  | RT x1, RT x2 -> 
      printf "runify: %s and %s@." x1 x2;
      raise CannotUnify
and eunify a b = 
  if Uf.equal a b then () else eunion a b 
      
let equal a b = Uf.tag a = Uf.tag b

module H = Hashtbl.Make (struct 
                           type t = node
                           let equal a b = Uf.tag a = Uf.tag b
                           let hash (x : t) : int = Hashtbl.hash (Uf.tag x)
                         end)
let to_ty, to_eff, to_r =
  let h = H.create 127 in
  let rec ty' = function
    | Ty.Var s -> Ty.var s
    | Ty.Arrow (t1,t2,e) -> Ty.arrow (ty t1) (ty t2) (eff e)
    | Ty.Tuple (t1,t2) -> Ty.tuple (ty t1) (ty t2)
    | Ty.Const c -> Ty.const c
    | Ty.Ref (r,t) -> Ty.ref_ (rv r) (ty t)
    | Ty.Map e -> Ty.map (eff e)
    | Ty.PureArr (t1,t2) -> Ty.parr (ty t1) (ty t2)
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
    | RT t -> t 
  and eff x =
    let f acc x = List.fold_left (fun acc x -> SS.add x acc) acc x in
    let rec aux ((racc,eacc) as acc) x = 
      match Uf.desc x with
      | EU -> acc
      | EV x -> racc, SS.add x eacc
      | ET (rl,el) -> List.fold_left aux (f racc (List.map rv rl),eacc) el in
    aux (SS.empty, SS.empty) x in
  ty, eff, rv

