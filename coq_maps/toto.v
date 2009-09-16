Set Implicit Arguments.
Require Import simple_map.
Open Scope Z_scope.
Require Omega.
Variable ref : forall (a : Set) (k : key), Set.
Definition ___get (A : Set) (k : key) (r : ref A k) (m : kmap) :=
    __get A k m.
Notation "!!" := (___get) (at level 50).

Section sec.
   Variable max: nat -> nat -> nat.
Variable min: nat -> nat -> nat.
Parameter array : forall (a : Set)  , Set.
Variable get: forall (a1 : Set)  , nat -> (array a1) -> a1.
Variable set: forall (a2 : Set)  , nat -> a2 -> (array a2) -> array a2.
Variable length: forall (a3 : Set)  , (array a3) -> nat.
Axiom update_length: forall (a4 : Set)  ,
 forall (t:array a4),
 forall (i:nat), forall (z:a4), (length t) = (length (set i z t)). 
Axiom get_set_eq: forall (a5 : Set)  ,
 forall (t1:array a5),
 forall (i1:nat),
 forall (z1:a5), (i1 < (length t1)) -> ((get i1 (set i1 z1 t1)) = z1). 
Axiom get_set_neq: forall (a6 : Set)  ,
 forall (t2:array a6),
 forall (i2:nat),
 forall (j:nat),
 forall (z2:a6),
 (i2 < (length t2)) ->
 ((j < (length t2)) -> ((i2 <> j) -> ((get i2 (set j z2 t2)) = (get i2 t2)))). 
Axiom length_nonnegative: forall (a7 : Set)  ,
 forall (t3:array a7), 0 <= (length t3). 
Variables r :
key.

Variable anon: kmap.
Variable x: ref nat r.
 
Section sec1.
   Variable anon1: kmap.
Variable i3: nat.
Hypothesis H: 1 <= i3.
Hypothesis H1: i3 <= 5.
Hypothesis H2: (!! x anon1) < (i3 * 10).
Variable anon2: kmap.
Hypothesis H3: (!! x anon1) = (!! x anon2).
Variable anon3: kmap.
Hypothesis H4: (!! x anon3) = ((!! x anon2) + i3).
 Lemma goal: (!! x anon3) < ((i3 + 1) * 10).

End sec1.

Lemma goal1: (!! x anon) < (1 * 10).

End sec.

