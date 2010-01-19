module Uf = Unionfind
module PT = Predefined.Ty

type ty = 
  | U
  | T of (node,rnode, effect) Ty.t'
and node = ty Uf.t
and rnode = r Uf.t
and r = 
  | RU 
  | RT of Name.t
and effect = rnode list * Name.S.t

let new_ty () = Uf.fresh U
let mkt t = Uf.fresh (T t)
let arrow t1 t2 e c = mkt (Ty.Arrow (t1,t2,e,c))
let tuple t1 t2 = mkt (Ty.Tuple (t1,t2)) 
let ref_ r t = mkt (Ty.Ref (r,t))
let mkr r = Uf.fresh (RT r)
let new_r () = Uf.fresh RU
let var s = mkt (Ty.App (s,([],[],[])))
let map e = mkt (Ty.Map e)
let app v i = mkt (Ty.App (v,i))
let parr t1 t2 = mkt (Ty.PureArr (t1,t2))

let eff_empty = [], Name.S.empty

let r_equal r1 r2 = 
  match Uf.desc r1, Uf.desc r2 with
  | RU, RU -> Uf.equal r1 r2
  | RU, RT _ | RT _, RU -> false
  | RT n1, RT n2 -> Name.equal n1 n2

let rremove (r,e) rl = 
  List.filter (fun x -> not (Misc.list_mem r_equal x rl)) r, e
let eff_union (r1,e1) (r2,e2) = 
  Misc.list_union r_equal r1 r2, Name.S.union e1 e2

let eff_union3 a b c = eff_union a (eff_union b c)


open Const
let const =
  let h = Hashtbl.create 5 in
  List.iter (fun c -> Hashtbl.add h c (mkt (Ty.Const c))) 
  [ TInt ; TUnit; TProp ];
  fun c -> Hashtbl.find h c

let prop = const TProp
let bool = var (PT.bool_var)
let int = const TInt
let unit = const TUnit

let union a b = Uf.union (fun a _ -> a) a b
open Myformat
let rec print_node fmt x = 
  match Uf.desc x with
  | U -> fprintf fmt "%d" (Uf.tag x)
  | T t -> 
      Ty.print' ~kind:`Who print_node prvar preff is_c fmt t
and is_c x = 
  match Uf.desc x with
  | U -> false
  | T t -> Ty.is_compound t
and prvar fmt x = 
  match Uf.desc x with
  | RU -> fprintf fmt "%d" (Uf.tag x)
  | RT x -> Name.print fmt x
and preff fmt (rl,el) = 
  fprintf fmt "{%a|" (print_list space prvar) rl;
  Name.S.iter (Name.print fmt) el;
  pp_print_string fmt "}"

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
      | Ty.Const c1, Ty.Const c2 when c1 = c2 -> ()
      | Ty.PureArr (ta1,ta2), Ty.PureArr (tb1,tb2)
      | Ty.Arrow (ta1,ta2,_,_), Ty.PureArr (tb1,tb2)
      | Ty.PureArr (ta1,ta2), Ty.Arrow (tb1,tb2,_,_)
      | Ty.Tuple (ta1,ta2), Ty.Tuple (tb1,tb2) -> 
          unify ta1 tb1;
          unify ta2 tb2
      | Ty.Arrow (ta1,ta2,e1,c1), Ty.Arrow (tb1,tb2,e2,c2) ->
          unify ta1 tb1;
          unify ta2 tb2;
          eunify e1 e2;
          List.iter2 runify c1 c2;
      | Ty.Ref (r1,t1), Ty.Ref (r2,t2) -> runify r1 r2; unify t1 t2
      | Ty.Map e1, Ty.Map e2 -> eunify e1 e2
      | Ty.App (v1,i1), Ty.App (v2,i2) when v1 = v2 ->
          Inst.iter2 unify runify eunify i1 i2
      | _ , _ -> raise CannotUnify
      end; 
      (* We really have to unify afterwards, in case of an exception being
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
(*       printf "runify: %a and %a@." prvar a prvar b; *)
      raise CannotUnify
and eunify (r1,e1) (r2,e2) = 
  if Effect.s_equal e1 e2 && Misc.list_equal_unsorted r_equal r1 r2 then ()
  else raise CannotUnify
      
module H = Hashtbl.Make (struct 
                           type t = node
                           let equal a b = Uf.tag a = Uf.tag b
                           let hash = Uf.tag
                         end)

let to_ty, to_eff, to_r =
  let h = H.create 127 in
  let rec ty' : (node, rnode, effect) Ty.t' -> Ty.t = function
    | Ty.Arrow (t1,t2,e,cap) -> 
        Ty.caparrow (ty t1) (ty t2) (eff e) (List.map rv cap)
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
  and eff (r,e) = Effect.from_u_effect (List.map rv r) e in
  ty, eff, rv

