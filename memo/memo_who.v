Set Implicit Arguments.
Section sec.
  
  Require Import WhoArith.
  Require Import WhoRef.
  Require Import WhoArray.
  Require Import WhoList.
  Definition hmap : forall (a b : Type)  , Type. 
  Admitted.
  Definition hmem: forall (a1 b1 : Type)  , a1 -> (hmap a1 b1) -> bool. 
  Admitted.
  Definition hget: forall (a2 b2 : Type)  , a2 -> (hmap a2 b2) -> b2. 
  Admitted.
  Definition hset: forall (a3 b3 : Type)  , a3 -> b3 -> (hmap a3 b3) -> hmap
    a3 b3. 
  Admitted.
  Axiom hgethset: forall (a4 b4 : Type)  ,
   forall (k:a4),
   forall (v:b4), forall (map:hmap a4 b4), (hget k (hset k v map)) = v. 
  Axiom hgethset2: forall (a5 b5 : Type)  ,
   forall (k1:a5),
   forall (k2:a5),
   forall (v1:b5),
   forall (map1:hmap a5 b5),
   (k1 <> k2) -> ((hget k1 (hset k2 v1 map1)) = (hget k1 map1)). 
  Axiom set_mem: forall (a6 b6 : Type)  ,
   forall (k11:a6),
   forall (k21:a6),
   forall (v2:b6),
   forall (map2:hmap a6 b6),
   ((hmem k11 (hset k21 v2 map2)) = true) ->
   ((k11 = k21) \/ ((hmem k11 map2) = true)). 
  Variables t : key.
  
  Variable t1: key. 
  Variable table: ref (hmap int int) t. 
  Variable f0: int -> int. 
  Variable t2: hmap int int. 
 Variable x: int. 
  Hypothesis H:
  forall (x1:int), ((hmem x1 t2) = true) -> ((hget x1 t2) = (f0 x1)). 
  Section sec1.
    Hypothesis H1: (hmem x t2) = true. 
    Lemma goal: (hget x t2) = (f0 x).
      auto. Qed.
    Section sec2.
      Variable x2: int. 
      Hypothesis H2: (hmem x2 t2) = true. 
      Lemma goal1: (hget x2 t2) = (f0 x2).
        auto. Qed.
      End sec2.
    End sec1.
  Section sec3.
    Hypothesis H3: ~ ((hmem x t2) = true). 
    Variable x3: int. 
    Hypothesis H4: (hmem x3 (hset x (f0 x) t2)) = true. 
    Lemma goal2: (hget x3 (hset x (f0 x) t2)) = (f0 x3).
      generalize (set_mem  H4); intros [A | A ].
        rewrite A, hgethset in *; auto.
        assert (x <> x3) by congruence.
        rewrite hgethset2; auto. 
    Qed.
    End sec3.
  End sec.
