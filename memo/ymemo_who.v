Set Implicit Arguments.
Section sec.
  
  Require Import WhoArith.
  Require Import WhoMap.
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
  Variable t2: hmap int int. 
  Definition table: ref (hmap int int) t. Admitted.
  Variable f0: int -> int. 
  Variable ff_pre : 
    ((int -> (hmap int int) -> Prop) * (int -> (hmap int int) ->
    (hmap int int) -> int -> Prop)) -> Prop.
  Variable ff_post:  ((int -> (hmap int int) ->
    Prop) * (int -> (hmap int int) -> (hmap int int) -> int -> Prop)) ->
    ((int -> (hmap int int) -> Prop) * (int -> (hmap int int) -> (hmap int
    int) -> int -> Prop)) -> Prop. 
  Hypothesis H:
  forall (k1:(int -> (hmap int int) -> Prop) * (int -> (hmap int int) ->
  (hmap int int) -> int -> Prop)),
  forall (r:(int -> (hmap int int) -> Prop) * (int -> (hmap int int) -> (hmap
  int int) -> int -> Prop)),
  ((forall (t3:hmap int int),
    forall (t4:hmap int int),
    forall (x:int),
    forall (r1:int),
    ((forall (x1:int), ((hmem x1 t3) = true) -> ((hget x1 t3) = (f0 x1))) ->
     (fst k1 x t3))
    /\
    ((snd k1 x t3 t4 r1) ->
     ((r1 = (f0 x)) /\
      (forall (x2:int), ((hmem x2 t4) = true) -> ((hget x2 t4) = (f0 x2))))))
   -> (ff_pre k1))
  /\
  ((ff_post k1 r) ->
   (forall (t5:hmap int int),
    forall (t6:hmap int int),
    forall (x3:int),
    forall (r2:int),
    ((forall (x4:int), ((hmem x4 t5) = true) -> ((hget x4 t5) = (f0 x4))) ->
     (fst r x3 t5))
    /\
    ((snd r x3 t5 t6 r2) ->
     ((r2 = (f0 x3)) /\
      (forall (x5:int), ((hmem x5 t6) = true) -> ((hget x5 t6) = (f0 x5))))))). 
  Variable t7: hmap int int. 
  Variable x6: int. 
  Hypothesis H1:
  forall (x7:int), ((hmem x7 t7) = true) -> ((hget x7 t7) = (f0 x7)). 
  Section sec1.
    Hypothesis H2: (hmem x6 t7) = true. 
    Lemma goal: (hget x6 t7) = (f0 x6).
      Proof. auto. Qed.
    Section sec2.
      Variable x8: int. 
      Hypothesis H3: (hmem x8 t7) = true. 
      Lemma goal1: (hget x8 t7) = (f0 x8).
        Proof. auto. Qed.
      End sec2.
    End sec1.
  Section sec3.

    Definition pk := (fun (_ : int) t => forall y, hmem y t = true -> hget y t = f0 y).
    Definition qk := ( fun (x11 : int) (_ t10 : hmap int int) (r3 : int) =>
     r3 = f0 x11 /\
     (forall x12 : int, hmem x12 t10 = true -> hget x12 t10 = f0 x12)).
    Hypothesis H4: ~ ((hmem x6 t7) = true). 
    Lemma goal2:
    ff_pre
    ((fun (x9:int) (t8:hmap int int) =>
     forall (x10:int), ((hmem x10 t8) = true) -> ((hget x10 t8) = (f0 x10)))
     ,
     (fun (x11:int) (t9:hmap int int) (t10:hmap int int) (r3:int),
     (r3 = (f0 x11)) /\
     (forall (x12:int),
      ((hmem x12 t10) = true) -> ((hget x12 t10) = (f0 x12))))).
    Proof.
      fold pk qk in *.
      generalize (H (pk,qk) (pk,qk)); simpl; intro K.
      apply K; unfold qk in *; intuition.
    Qed.
      
    Section sec4.
      Variable anon: (int -> (hmap int int) -> Prop) * (int -> (hmap int
        int) -> (hmap int int) -> int -> Prop). 
      Hypothesis H5:
      ff_post
      ((λ(x13:int) =>
       (λ(t11:hmap int int) =>
       forall (x14:int),
       ((hmem x14 t11) = true) -> ((hget x14 t11) = (f0 x14)))) ,
       (λ(x15:int) =>
       (λ(t12:hmap int int) =>
       (λ(t13:hmap int int) =>
       (λ(r4:int) =>
       (r4 = (f0 x15)) /\
       (forall (x16:int),
        ((hmem x16 t13) = true) -> ((hget x16 t13) = (f0 x16))))))))
      anon. 
      Lemma goal3: fst anon x6 t7.
      Proof.
        fold pk qk in *.
        generalize (H (pk,qk) anon); simpl; intros [ K1 K2].
        clear H. apply (K2 H5 t7 t7 x6 x6). auto.
      Qed.
      Section sec5.
        Variable t14: hmap int int. 
        Variable anon1: int. 
        Hypothesis H6: snd anon x6 t7 t14 anon1. 
        Lemma goal4: anon1 = (f0 x6).
        Proof.
          fold pk qk in *.
          generalize (H (pk,qk) anon); simpl; intros [ K1 K2].
          clear H. apply (K2 H5 t7 t14 x6 anon1). auto.
        Qed.
        Section sec6.
          Variable x17: int. 
          Hypothesis H7: (hmem x17 (hset x6 anon1 t14)) = true. 
          Lemma goal5: (hget x17 (hset x6 anon1 t14)) = (f0 x17).
          Proof. 
          fold pk qk in *.
          generalize (H (pk,qk) anon); simpl; intros [ K1 K2].
          clear H. generalize (K2 H5 t7 t14 x6 anon1); intros Q.
          case_eq (Z_eq_dec x17 x6); intros A _.
          subst. rewrite hgethset; apply Q; auto.
          rewrite hgethset2; auto. apply Q; auto. 
          generalize (set_mem H7); intros [ B | B]; auto. 
          Qed.
        
          End sec6.
        End sec5.
      End sec4.
    End sec3.
  End sec.
