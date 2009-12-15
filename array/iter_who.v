Set Implicit Arguments.
Section sec.
  Require Import WhoArith.
  Require Import WhoMap.
  Require Import WhoArray.
  Require Import WhoList.
  Variables a e : Type.
  
  Variable r:  key. 
  Variable inv:  (array a) -> e -> int -> Prop. 
  Variable f:  (a -> (array a) -> e -> Prop) * (a -> (array a) -> e -> (array
    a) -> e -> unit -> Prop). 
  Variable e1:  e. 
  Variable r1:  array a. 
  Hypothesis H:  inv r1 e1 0. 
  Hypothesis H1:
     forall (i:int),
     (0 <= i) ->
     ((i < (len r1)) ->
      (forall (e2:e),
       forall (r2:array a),
       (inv r2 e2 i) ->
       ((fst f (get i r2) r2 e2) /\
        (forall (e3:e),
         forall (r3:array a),
         (snd f (get i r2) r2 e2 r3 e3 tt) -> (inv r3 e3 (i + 1)))))). 
  Section sec1.
    Variable e4:  e. 
    Variable r4:  array a. 
    Variable i1:  int. 
    Hypothesis H2:  0 <= i1. 
    Hypothesis H3:  i1 <= ((len r1) - 1). 
    Hypothesis H4:  inv r4 e4 i1. 
    Lemma goal: fst f (get i1 r4) r4 e4.
      Proof.
        assert ( T : i1 < len r1) by omega.
        generalize (H1 H2 T); intro K. apply (K e4 r4 H4). Qed.
      
    Section sec2.
      Variable e5:  e. 
      Variable r5:  array a. 
      Hypothesis H5:  snd f (get i1 r4) r4 e4 r5 e5 tt. 
      Lemma goal1: inv r5 e5 (i1 + 1).
        Proof.
        assert ( T : i1 < len r1) by omega.
        generalize (H1 H2 T); intro K. apply (K e4 r4 H4); auto. Qed.
        
      End sec2.
    End sec1.
  Section sec3.
    Variable e6:  e. 
    Variable r6:  array a. 
    Hypothesis H6:  inv r6 e6 (max 0 (((len r1) - 1) + 1)). 
    Lemma goal2: inv r6 e6 (len r1).
      Proof.
      cut (max 0 (len r1 - 1 + 1) = len r1).
      intro K; rewrite K in *; auto.
      assert (T : len r1 - 1 + 1 = len r1) by omega.
      rewrite T. apply Zmax_right. apply len_nonnegative. 
      Qed.
    End sec3.
  End sec.
