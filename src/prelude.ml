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

let prelude = "
section boolean
  coq predefined
  pangoline takeover
  type bool
  logic true : bool
  logic false : bool
end

section singleton
  coq predefined
  pangoline takeover
  type unit
  logic tt : unit
end

section basiclogic
  coq predefined
  pangoline predefined
  logic /\\ : prop -> prop -> prop
  logic \\/ : prop -> prop -> prop
  logic -> : prop -> prop -> prop
  logic ~ : prop -> prop
  logic = ['a||] : 'a -> 'a -> prop
end

section encoding
  coq takeover
  pangoline takeover
  type region ['u||]
  type refty ['reg 'ty||]

  logic ref_get ['reg 'u||] : 'reg region -> ('reg,'u) refty -> 'u
end
section tuples
  coq predefined
  pangoline predefined

  logic mk_2tuple ['a 'b||] : 'a -> 'b -> 'a * 'b
  logic mk_3tuple ['a 'b 'c||] : 'a -> 'b -> 'c -> 'a * 'b * 'c
  logic mk_4tuple ['a 'b 'c 'd||] :
    'a -> 'b -> 'c -> 'd -> 'a * 'b * 'c * 'd
  logic mk_5tuple ['a 'b 'c 'd 'e||] :
    'a -> 'b -> 'c -> 'd -> 'e -> 'a * 'b * 'c * 'd * 'e
  logic mk_6tuple ['a 'b 'c 'd 'e 'f||] :
    'a -> 'b -> 'c -> 'd -> 'e -> 'f-> 'a * 'b * 'c * 'd * 'e * 'f
  logic mk_7tuple ['a 'b 'c 'd 'e 'f 'g||] :
    'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'a * 'b * 'c * 'd * 'e * 'f * 'g

  logic get_2_1_tuple ['a 'b||] : 'a * 'b -> 'a
  logic get_2_2_tuple ['a 'b||] : 'a * 'b -> 'b

  logic get_3_1_tuple ['a 'b 'c||] : 'a * 'b * 'c -> 'a
  logic get_3_2_tuple ['a 'b 'c||] : 'a * 'b * 'c -> 'b
  logic get_3_3_tuple ['a 'b 'c||] : 'a * 'b * 'c -> 'c

  logic get_4_1_tuple ['a 'b 'c 'd||] : 'a * 'b * 'c * 'd -> 'a
  logic get_4_2_tuple ['a 'b 'c 'd||] : 'a * 'b * 'c * 'd -> 'b
  logic get_4_3_tuple ['a 'b 'c 'd||] : 'a * 'b * 'c * 'd -> 'c
  logic get_4_4_tuple ['a 'b 'c 'd||] : 'a * 'b * 'c * 'd -> 'd

  logic get_5_1_tuple ['a 'b 'c 'd 'e||] : 'a * 'b * 'c * 'd * 'e -> 'a
  logic get_5_2_tuple ['a 'b 'c 'd 'e||] : 'a * 'b * 'c * 'd * 'e -> 'b
  logic get_5_3_tuple ['a 'b 'c 'd 'e||] : 'a * 'b * 'c * 'd * 'e -> 'c
  logic get_5_4_tuple ['a 'b 'c 'd 'e||] : 'a * 'b * 'c * 'd * 'e -> 'd
  logic get_5_5_tuple ['a 'b 'c 'd 'e||] : 'a * 'b * 'c * 'd * 'e -> 'e

  logic get_6_1_tuple ['a 'b 'c 'd 'e 'f||] : 'a * 'b * 'c * 'd * 'e * 'f -> 'a
  logic get_6_2_tuple ['a 'b 'c 'd 'e 'f||] : 'a * 'b * 'c * 'd * 'e * 'f -> 'b
  logic get_6_3_tuple ['a 'b 'c 'd 'e 'f||] : 'a * 'b * 'c * 'd * 'e * 'f -> 'c
  logic get_6_4_tuple ['a 'b 'c 'd 'e 'f||] : 'a * 'b * 'c * 'd * 'e * 'f -> 'd
  logic get_6_5_tuple ['a 'b 'c 'd 'e 'f||] : 'a * 'b * 'c * 'd * 'e * 'f -> 'e
  logic get_6_6_tuple ['a 'b 'c 'd 'e 'f||] : 'a * 'b * 'c * 'd * 'e * 'f -> 'f

  logic get_7_1_tuple ['a 'b 'c 'd 'e 'f 'g||] :
      'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'a
  logic get_7_2_tuple ['a 'b 'c 'd 'e 'f 'g||] :
      'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'b
  logic get_7_3_tuple ['a 'b 'c 'd 'e 'f 'g||] :
      'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'c
  logic get_7_4_tuple ['a 'b 'c 'd 'e 'f 'g||] :
      'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'd
  logic get_7_5_tuple ['a 'b 'c 'd 'e 'f 'g||] :
      'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'e
  logic get_7_6_tuple ['a 'b 'c 'd 'e 'f 'g||] :
      'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'f
  logic get_7_7_tuple ['a 'b 'c 'd 'e 'f 'g||] :
      'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'g

end
section arith
  coq \"WhoArith\"
  pangoline takeover
  logic + : int -> int -> int
  logic - : int -> int -> int
  logic * : int -> int -> int
  logic < : int -> int -> prop
  logic <= : int -> int -> prop
  logic > : int -> int -> prop
  logic >= : int -> int -> prop
  logic << : int -> int -> bool
  logic <<= : int -> int -> bool
  logic >> : int -> int -> bool
  logic >>= : int -> int -> bool
  logic <> ['a||] : 'a -> 'a -> prop
  logic int_max : int -> int -> int
  logic int_min : int -> int -> int
  logic band : bool -> bool -> bool
  logic bor : bool -> bool -> bool

  axiom int_max_is_ge :
    forall (x y :int).
      int_max x y >= x /\\ int_max x y >= y

  axiom int_max_is_some :
    forall (x y : int).
      int_max x y = x \\/ int_max x y = y

  axiom int_min_is_le :
    forall (x y : int).
      int_min x y <= x /\\ int_min x y <= y

  axiom int_min_is_some :
    forall (x y : int).
      int_min x y = x \\/ int_min x y = y

end

section beq
  coq predefined
  pangoline takeover

  logic == ['a||] : 'a -> 'a -> bool
  logic != ['a||] : 'a -> 'a -> bool
end

parameter assert (f : prop) : unit,{} = { f } { f }
parameter check (f : prop) : unit, {} = { f } { }
parameter assume (f : prop) : unit,{} = {  }  { f }

section Whoref
  coq \"WhoMap\"
  pangoline predefined

  logic !! ['a|r|'e] : ref(r,'a) -> <r 'e > -> 'a
  parameter ! ['a|r|] (x : ref(r,'a)) : 'a, {r} =
    {}
    {r : !!x = r /\\ !!x|old = !!x}

  parameter := ['a|r|] (x : ref(r,'a)) (v : 'a) : unit, {r} =
    {}
    { !!x = v}

  parameter ref ['a|r|] (v : 'a) : ref(r,'a), {r} = allocates r
    {}
    { x : !!x = v }

  logic combine [||'e1 'e2 'e3] : <'e1 'e2> -> <'e2 'e3> -> <'e1 'e2 'e3>
  logic restrict [||'e1 'e2] : <'e1 'e2> -> <'e2>
  logic empty : < >

  let fst ['a 'b] (x : 'a * 'b) = get_2_1_tuple x
  let snd ['a 'b] (x : 'a * 'b) = get_2_2_tuple x
  let pre ['a 'b||] (x : 'a * 'b) = get_2_1_tuple x
  let post ['a 'b||] (x : 'a * 'b) = get_2_2_tuple x

end

parameter forto [||'e] (inv : int -> <'e> -> prop) (start end_ : int)
  (f : int ->{'e} unit) : unit, {'e} =
    { inv start cur /\\
          forall (i : int). start <= i /\\ i <= end_ ->
          forall (m : <'e>) . inv i m -> pre f i m /\\
          forall (n : <'e>). post f i m n () -> inv (i+1) n
    }
    { inv (int_max start (end_ + 1)) cur}


parameter fordownto [||'e] (inv :  int -> <'e> -> prop) (start end_ : int)
  (f : int ->{'e} unit) : unit, {'e} =
    { inv start cur /\\
          forall (i : int). end_ <= i /\\ i <= start ->
          forall (m : <'e>) . inv i m -> pre f i m /\\
          forall (n : <'e>). post f i m n () -> inv (i-1) n
    }
    { inv (int_min start (end_ - 1)) cur }

section Array
  coq \"WhoArray\"
  pangoline takeover
  type array ['a||]

  logic ar_empty ['a||] : 'a array
  logic get ['a||] : int -> 'a array -> 'a
  logic set ['a||]: int -> 'a -> 'a array -> 'a array
  logic len ['a||] :  'a array -> int
  logic create ['a||] :  int -> 'a -> 'a array

  axiom update_length ['a||] :
    forall (t : 'a array) (i : int) (z : 'a).
    0 <= i /\\ i < len t -> len t = len (set i z t)

  axiom get_set_eq ['a||] :
    forall (t : 'a array) (i : int) (z : 'a).
      0 <= i /\\ i < len t -> get i (set i z t) = z

  axiom length_empty ['a||] : len (ar_empty : 'a array) = 0

  axiom get_set_neq ['a||] :
    forall (t : 'a array ) (i : int) (j : int) (z : 'a).
      (0 <= i /\\ i < len t) ->
      (0 <= j /\\ j < len t) ->
        i <> j -> get i (set j z t) = get i t

  axiom length_nonnegative ['a||] :
    forall (t : array ['a||]).  0 <= len t

  axiom length_create ['a||] :
    forall (l : int) (v : 'a). 0 <= l -> len (create l v) = l

  axiom create_access ['a||] :
    forall (i l : int) (v : 'a).
      0 <= i -> i < l -> get i (create l v) = v
end

section List
  coq \"WhoList\"
  pangoline takeover
  type list ['a||]

  logic nil ['a||] : 'a list
  logic cons ['a||] : 'a -> 'a list -> 'a list

  logic is_nil ['a||] : 'a list -> bool
  logic l_in ['a||] : 'a -> 'a list -> prop
end

"

