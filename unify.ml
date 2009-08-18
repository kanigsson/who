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
let ref_ r t = mkt (Ty.Ref (r,t))
let mkr r = Uf.fresh (RT r)
let new_r () = Uf.fresh RU
let var s = mkt (Ty.Var s)
let map e = mkt (Ty.Map e)
let app v i = mkt (Ty.App (v,i))
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
let bool = const TBool
let int = const TInt
let unit = const TUnit

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
  | T t -> Ty.print' print_node prvar preff is_c fmt t
and is_c x = 
  match Uf.desc x with
  | U -> false
  | T t -> Ty.is_compound t
and prvar fmt x = 
  match Uf.desc x with
  | RU -> fprintf fmt "%d" (Uf.tag x)
  | RT s -> fprintf fmt "%s" s
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
(*   printf "unify: %a and %a@." print_node a print_node b; *)
  if Uf.equal a b then () else
  match Uf.desc a, Uf.desc b with
  | U, U -> union a b
  | U , T _ -> union b a
  | T _, U -> union a b
  | T t1, T t2 ->
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
      | Ty.Ref (r1,t1), Ty.Ref (r2,t2) -> runify r1 r2; unify t1 t2
      | Ty.Map e1, Ty.Map e2 -> eunify e1 e2
      | Ty.App (v1,i1), Ty.App (v2,i2) when v1 = v2 ->
          Inst.iter2 unify runify eunify i1 i2
      | _ , _ -> 
          raise CannotUnify
      end; 
      (* We really should unify afterwards, in case of an exception beeing
       * raised *)
      union a b;
and runify a b = 
(*   printf "runify: %a and %a@." prvar a prvar b; *)
  if Uf.equal a b then () else
  match Uf.desc a, Uf.desc b with
  | RU, RU -> union a b
  | RU , RT _ -> union b a
  | RT _, RU -> union a b
  | RT s1, RT s2 when s1 = s2 -> ()
  | RT _, RT _ -> 
(*       printf "runify: %s and %s@." x1 x2; *)
      raise CannotUnify
and eunify a b = 
  if Uf.equal a b then () else eunion a b 
      
module H = Hashtbl.Make (struct 
                           type t = node
                           let equal a b = Uf.tag a = Uf.tag b
                           let hash = Uf.tag
                         end)

let to_ty, to_eff, to_r =
  let h = H.create 127 in
  let rec ty' : (node, rnode, enode) Ty.t' -> Ty.t = function
    | Ty.Var s -> Ty.var s
    | Ty.Arrow (t1,t2,e) -> Ty.arrow (ty t1) (ty t2) (eff e)
    | Ty.Tuple (t1,t2) -> Ty.tuple (ty t1) (ty t2)
    | Ty.Const c -> Ty.const c
    | Ty.Ref (r,t) -> Ty.ref_ (rv r) (ty t)
    | Ty.Map e -> Ty.map (eff e)
    | Ty.PureArr (t1,t2) -> Ty.parr (ty t1) (ty t2)
    | Ty.App (v,i) -> Ty.app v (Inst.map ty rv eff i) 
  and ty x = 
    try H.find h x 
    with Not_found -> 
      match Unionfind.desc x with
      | U -> assert false
      | T t -> 
          let r = ty' t in
          H.add h x r; r
  and rv r = 
    match Uf.desc r with
    | RU -> assert false
    | RT s -> s
  and eff x =
    let f acc x = List.fold_left (fun acc x -> SS.add x acc) acc x in
    let rec aux ((racc,eacc) as acc) x = 
      match Uf.desc x with
      | EU -> acc
      | EV x -> racc, SS.add x eacc
      | ET (rl,el) -> List.fold_left aux (f racc (List.map rv rl),eacc) el in
    aux (SS.empty, SS.empty) x in
  ty, eff, rv

