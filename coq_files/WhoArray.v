Set Implicit Arguments.
Require Import WhoArith.
Parameter array : forall (a1 : Type)  , Type.
Parameter get: forall (a2 : Type)  , int -> array a2 -> a2.

Parameter set: 
  forall (a3 : Type)  , int -> a3 -> array a3 -> array a3.
Parameter len: forall (a4 : Type)  , array a4 -> int.

Axiom update_len: 
  forall (a5 : Type) (t:array a5) (i4:int) (z:a5), 
    len t = len (set i4 z t).

Axiom get_set_eq: 
  forall (a6 : Type) (t1:array a6) (i5:int) (z1:a6),
         i5 < len t1 -> get i5 (set i5 z1 t1) = z1.

Axiom get_set_neq: 
  forall (a7 : Type) (t2:array a7) (i6:int)(j:int) (z2:a7),
    i6 < len t2 -> j < len t2 ->
       i6 <> j -> get i6 (set j z2 t2) = get i6 t2.

Axiom len_nonnegative: 
  forall (a8 : Type) (t3:array a8), 0 <= len t3.  
