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
exception CannotUnify

open Format
let rec unify a b =
(*   printf "unify: %a and %a@." print_node a print_node b; *)
  if Uf.equal a b then () else
  begin match Uf.desc a, Uf.desc b with
  | U, U -> union a b
  | U , _ -> union b a
  | _, U -> union a b
  | Const c1, Const c2 when c1 = c2 -> ()
  | PureArr (ta1,ta2), PureArr (tb1,tb2)
  | Arrow (ta1,ta2,_,_), PureArr (tb1,tb2)
  | PureArr (ta1,ta2), Arrow (tb1,tb2,_,_) ->
      unify ta1 tb1;
      unify ta2 tb2
  | Arrow (ta1,ta2,e1,c1), Arrow (tb1,tb2,e2,c2) ->
      unify ta1 tb1;
      unify ta2 tb2;
      eunify e1 e2;
      List.iter2 runify c1 c2;
  | Tuple tl1, Tuple tl2 when List.length tl1 = List.length tl2 ->
      List.iter2 unify tl1 tl2
  | Ref (r1,t1), Ref (r2,t2) -> runify r1 r2; unify t1 t2
  | Map e1, Map e2 -> eunify e1 e2
  | App (v1,i1), App (v2,i2) when v1 = v2 ->
      begin try List.iter2 unify i1 i2
      with Invalid_argument _ -> raise CannotUnify end
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
  if Effect.s_equal e1 e2 && ExtList.equal_unsorted r_equal r1 r2 then ()
  else raise CannotUnify

