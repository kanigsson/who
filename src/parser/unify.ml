(******************************************************************************)
(*                                                                            *)
(*                      Who                                                   *)
(*                                                                            *)
(*       A simple VCGen for higher-order programs.                            *)
(*                                                                            *)
(*  Copyright (C) 2009, 2010, Johannes Kanig                                  *)
(*  Contact: kanig@lri.fr                                                     *)
(*                                                                            *)
(*  Who is free software: you can redistribute it and/or modify it under the  *)
(*  terms of the GNU Lesser General Public License as published by the Free   *)
(*  Software Foundation, either version 3 of the License, or any later        *)
(*  version.                                                                  *)
(*                                                                            *)
(*  Who is distributed in the hope that it will be useful, but WITHOUT ANY    *)
(*  WARRANTY; without even the implied warranty of MERCHANTABILITY or         *)
(*  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public      *)
(*  License for more details.                                                 *)
(*                                                                            *)
(*  You should have received a copy of the GNU Lesser General Public License  *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>      *)
(******************************************************************************)

module Uf = Unionfind

open MutableType

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
      | Ty.PureArr (ta1,ta2), Ty.Arrow (tb1,tb2,_,_) ->
          unify ta1 tb1;
          unify ta2 tb2
      | Ty.Arrow (ta1,ta2,e1,c1), Ty.Arrow (tb1,tb2,e2,c2) ->
          unify ta1 tb1;
          unify ta2 tb2;
          eunify e1 e2;
          List.iter2 runify c1 c2;
      | Ty.Tuple tl1, Ty.Tuple tl2 when List.length tl1 = List.length tl2 ->
          List.iter2 unify tl1 tl2
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

