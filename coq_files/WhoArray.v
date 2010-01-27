Set Implicit Arguments.
Require Import WhoArith.
Parameter array : forall (a1 : Type)  , Type.
Parameter get: forall (a2 : Type)  , int -> array a2 -> a2.
Parameter create : forall (a2 : Type), int -> a2 -> array a2.
Parameter empty : forall (a :Type), array a.

Parameter set: 
  forall (a3 : Type)  , int -> a3 -> array a3 -> array a3.
Parameter len: forall (a4 : Type)  , array a4 -> int.

Axiom len_empty : 
  forall a, len (empty a) = 0.
Axiom update_len: 
  forall (a5 : Type) (t:array a5) (i4:int) (z:a5), 
    0 <= i4 < len t -> len t = len (set i4 z t).

Axiom get_set_eq: 
  forall (a6 : Type) (t1:array a6) (i5:int) (z1:a6),
         0 <= i5 < len t1 -> get i5 (set i5 z1 t1) = z1.

Axiom get_set_neq: 
  forall (a7 : Type) (t2:array a7) (i6:int)(j:int) (z2:a7),
    0 <= i6 < len t2 -> 0 <= j < len t2 ->
       i6 <> j -> get i6 (set j z2 t2) = get i6 t2.

Axiom len_nonnegative: 
  forall (a8 : Type) (t3:array a8), 0 <= len t3.  

Axiom len_create:
  forall (a : Type) (k : a) (l : int),
    0 <= l -> len (create l k) = l.

Axiom create_access:
  forall (a : Type) (k : a) (l i : int),
    0 <= i < l -> get i (create l k) = k.
    
