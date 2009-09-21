Set Implicit Arguments.
Require Import WhoArith.
Require Import WhoArray.
Require Import WhoList.
Parameter hashkey : Type.
Parameter hash : hashkey  -> int. 

Parameter h_eq_dec : 
  forall (a b : hashkey), {a = b} + {a <> b}.

Definition hl (a : Type) := list (hashkey* a).
Definition ht (a : Type) := array (hl a).
Fixpoint find (a : Type) (k : hashkey) (l : hl a) {struct l} :=
  match l with
    | nil => None
    | (k',v) :: xs => 
      if h_eq_dec k k' then Some v else 
        find k xs
  end.

Definition repr (a : Type) (h : ht a) (l : hl a) :=
  forall k v i, In (k,v) (get i h) -> 
    find k (get i h) = find k l.

