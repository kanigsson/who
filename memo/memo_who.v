Set Implicit Arguments.
Section sec.
  
  Require Import WhoArith.
  Require Import WhoMap.
  Require Import WhoArray.
  Require Import WhoList.
<<<<<<< memo_who.v.bak
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
||||||| memo_who.v.orig.old
  Definition hmap : forall (a b : Type)  , Type. 
  Definition hmem: forall (a1 b1 : Type)  , a1 -> (hmap a1 b1) -> bool. 
  Definition hget: forall (a2 b2 : Type)  , a2 -> (hmap a2 b2) -> b2. 
  Definition hset: forall (a3 b3 : Type)  , a3 -> b3 -> (hmap a3 b3) -> hmap
    a3 b3. 
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
=======
  Definition hmap : forall (a23 b3 : Type)  , Type. 
  Definition hmem2: forall (a24 b4 : Type)  , a24 -> (hmap a24 b4) -> bool. 
  Definition hget2: forall (a25 b5 : Type)  , a25 -> (hmap a25 b5) -> b5. 
  Definition hset2: forall (a26 b6 : Type)  , a26 -> b6 -> (hmap a26 b6) ->
    hmap a26 b6. 
  Axiom hgethset2: forall (a27 b7 : Type)  ,
   forall (k:a27),
   forall (v:b7), forall (map:hmap a27 b7), (hget2 k (hset2 k v map)) = v. 
  Axiom hgethset22: forall (a28 b8 : Type)  ,
   forall (k1:a28),
   forall (k2:a28),
   forall (v1:b8),
   forall (map1:hmap a28 b8),
   (k1 <> k2) -> ((hget2 k1 (hset2 k2 v1 map1)) = (hget2 k1 map1)). 
  Axiom set_mem2: forall (a29 b9 : Type)  ,
   forall (k11:a29),
   forall (k21:a29),
   forall (v2:b9),
   forall (map2:hmap a29 b9),
   ((hmem2 k11 (hset2 k21 v2 map2)) = true) ->
   ((k11 = k21) \/ ((hmem2 k11 map2) = true)). 
  Variables t4 : key.
>>>>>>> memo_who.v.orig
  
  Variable t10: key. 
  Variable table2: ref (hmap int int) t4. 
  Variable f02: int -> int. 
  Variable t11: hmap int int. 
  Variable x8: int. 
  Hypothesis H:
  forall (x9:int), ((hmem2 x9 t11) = true) -> ((hget2 x9 t11) = (f02 x9)). 
  Section sec1.
<<<<<<< memo_who.v.bak
    Hypothesis H1: (hmem x t2) = true. 
    Lemma goal: (hget x t2) = (f0 x).
      Proof. auto. Qed.
||||||| memo_who.v.orig.old
    Hypothesis H1: (hmem x t2) = true. 
    Lemma goal: (hget x t2) = (f0 x).
=======
    Hypothesis H1: (hmem2 x8 t11) = true. 
    Lemma goal: (hget2 x8 t11) = (f02 x8).
>>>>>>> memo_who.v.orig
    Section sec2.
<<<<<<< memo_who.v.bak
      Variable x2: int. 
      Hypothesis H2: (hmem x2 t2) = true. 
      Lemma goal1: (hget x2 t2) = (f0 x2).
       Proof. auto. Qed.
||||||| memo_who.v.orig.old
      Variable x2: int. 
      Hypothesis H2: (hmem x2 t2) = true. 
      Lemma goal1: (hget x2 t2) = (f0 x2).
=======
      Variable x10: int. 
      Hypothesis H2: (hmem2 x10 t11) = true. 
      Lemma goal1: (hget2 x10 t11) = (f02 x10).
>>>>>>> memo_who.v.orig
      End sec2.
    End sec1.
  Section sec3.
<<<<<<< memo_who.v.bak
    Hypothesis H3: ~ ((hmem x t2) = true). 
    Variable x3: int. 
    Hypothesis H4: (hmem x3 (hset x (f0 x) t2)) = true. 
    Lemma goal2: (hget x3 (hset x (f0 x) t2)) = (f0 x3).
      Proof.
        generalize (set_mem H4); intros [A | A].
        subst; rewrite hgethset; auto.
        case_eq (Z_eq_dec x x3); intros; try congruence.
        rewrite hgethset2; auto.
     Qed.
||||||| memo_who.v.orig.old
    Hypothesis H3: ~ ((hmem x t2) = true). 
    Variable x3: int. 
    Hypothesis H4: (hmem x3 (hset x (f0 x) t2)) = true. 
    Lemma goal2: (hget x3 (hset x (f0 x) t2)) = (f0 x3).
=======
    Hypothesis H3: ~ ((hmem2 x8 t11) = true). 
    Variable x11: int. 
    Hypothesis H4: (hmem2 x11 (hset2 x8 (f02 x8) t11)) = true. 
    Lemma goal2: (hget2 x11 (hset2 x8 (f02 x8) t11)) = (f02 x11).
>>>>>>> memo_who.v.orig
    End sec3.
  End sec.
