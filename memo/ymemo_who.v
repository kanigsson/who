Set Implicit Arguments.
Require Import WhoArith.
Require Import WhoArray.
Require Import WhoList.
Definition hmap : forall (a b : Type)  , Type. Admitted.
Definition hmem: forall (a1 b1 : Type)  ,  (a1) -> (hmap (a1) (b1)) ->
  bool.
  Proof.
  Admitted.
   
Definition hget: forall (a2 b2 : Type)  ,  (a2) -> (hmap (a2) (b2)) ->
  b2.
  Proof.
  Admitted.
   
Definition hset: forall (a3 b3 : Type)  ,  (a3) -> (b3) -> (hmap (a3)
  (b3)) -> hmap (a3) (b3).
  Proof.
  Admitted.
   
Hypothesis hgethset: forall (a4 b4 : Type),
  forall (k:a4),
  forall (v:b4), forall (map:hmap (a4) (b4)), (hget k (hset k v map)) = v . 
Hypothesis hgethset1: forall (a5 b5 : Type),
  forall (k1:a5),
  forall (k2:a5),
  forall (v1:b5),
  forall (map1:hmap (a5) (b5)),
  (k1 <> k2) -> ((hget k1 (hset k2 v1 map1)) = (hget k1 map1)) . 
Hypothesis set_mem: forall (a6 b6 : Type),
  forall (k3:a6),
  forall (k4:a6),
  forall (v2:b6),
  forall (map2:hmap (a6) (b6)),
  ((hmem k3 (hset k4 v2 map2)) = true) ->
  ((k3 = k4) \/ ((hmem k3 map2) = true)) . 
Section sec.
   Variable f:  Z -> Z. 
  Variable ff:  (((Z -> (hmap Z Z) -> Prop) * (Z -> (hmap Z Z) -> (hmap Z
    Z) -> Z -> Prop)) -> Prop) * (((Z -> (hmap Z Z) -> Prop) * (Z -> (hmap Z
    Z) -> (hmap Z Z) -> Z -> Prop)) -> ((Z -> (hmap Z Z) -> Prop) * (Z ->
    (hmap Z Z) -> (hmap Z Z) -> Z -> Prop)) -> Prop). 
  Hypothesis H:
    forall (k5:(Z -> (hmap Z Z) -> Prop) * (Z -> (hmap Z Z) -> (hmap Z Z) ->
    Z -> Prop)),
    (forall (x:Z),
     forall (t:hmap Z Z),
     (forall (x1:Z), ((hmem x1 t) = true) -> ((hget x1 t) = (f x1))) ->
     ((fst k5 x t) /\
      (forall (t1:hmap Z Z),
       forall (anon:Z),
       (snd k5 x t t1 anon) ->
       ((anon = (f x)) /\
        (forall (x2:Z), ((hmem x2 t1) = true) -> ((hget x2 t1) = (f x2)))))))
    ->
    ((fst ff k5) /\
     (forall (anon1:(Z -> (hmap Z Z) -> Prop) * (Z -> (hmap Z Z) -> (hmap Z
      Z) -> Z -> Prop)),
      (snd ff k5 anon1) ->
      (forall (x3:Z),
       forall (t2:hmap Z Z),
       (forall (x4:Z), ((hmem x4 t2) = true) -> ((hget x4 t2) = (f x4))) ->
       ((fst anon1 x3 t2) /\
        (forall (t3:hmap Z Z),
         forall (anon2:Z),
         (snd anon1 x3 t2 t3 anon2) ->
         ((anon2 = (f x3)) /\
          (forall (x5:Z), ((hmem x5 t3) = true) -> ((hget x5 t3) = (f x5))))))))). 
  Variable x6:  Z. 
  Variable t4:  hmap Z Z. 
  Hypothesis H1:
    forall (x7:Z), ((hmem x7 t4) = true) -> ((hget x7 t4) = (f x7)). 
  Section sec1.
     Hypothesis H2: (hmem x6 t4) = true. 
    Lemma goal: (hget x6 t4) = (f x6).
      Proof. auto. Qed.
      
    Section sec2.
       Variable x8:  Z. 
      Hypothesis H3: (hmem x8 t4) = true. 
      Lemma goal1: (hget x8 t4) = (f x8).
        Proof. auto. Qed.
         End sec2. End sec1.
   Definition myfun := 
     (fun (_ : int) (t5 : hmap int int) =>
      forall x10 : int, hmem x10 t5 = true -> hget x10 t5 = f x10,
     fun (x11 : int) (_ t7 : hmap int int) (r : int) =>
     r = f x11 /\
     (forall x12 : int, hmem x12 t7 = true -> hget x12 t7 = f x12)).
 
  Section sec3.
     Hypothesis H4: (hmem x6 t4) = false. 
    Lemma goal2:
      fst ff
      ((fun (x9:Z) =>
       (fun (t5:hmap Z Z) =>
       forall (x10:Z), ((hmem x10 t5) = true) -> ((hget x10 t5) = (f x10))))
       ,
       (fun (x11:Z) =>
       (fun (t6:hmap Z Z) =>
       (fun (t7:hmap Z Z) =>
       (fun (r:Z) =>
       (r = (f x11)) /\
       (forall (x12:Z), ((hmem x12 t7) = true) -> ((hget x12 t7) = (f x12)))))))).
      Proof.
        generalize (H myfun); clear H; intuition. apply H.
        unfold myfun; simpl; intuition.
      Qed.
      
    Section sec4.
       Variable anon3:  (Z -> (hmap Z Z) -> Prop) * (Z -> (hmap Z Z) -> (hmap
         Z Z) -> Z -> Prop). 
      Hypothesis H5:
        snd ff
        ((fun (x13:Z) =>
         (fun (t8:hmap Z Z) =>
         forall (x14:Z), ((hmem x14 t8) = true) -> ((hget x14 t8) = (f x14))))
         ,
         (fun (x15:Z) =>
         (fun (t9:hmap Z Z) =>
         (fun (t10:hmap Z Z) =>
         (fun (r1:Z) =>
         (r1 = (f x15)) /\
         (forall (x16:Z),
          ((hmem x16 t10) = true) -> ((hget x16 t10) = (f x16))))))))
        anon3. 

     Lemma K :
    (forall (x : int) (t : hmap int int),
       (forall x1 : int, hmem x1 t = true -> hget x1 t = f x1) ->
       fst myfun x t /\
       (forall (t1 : hmap int int) (anon : int),
        snd myfun x t t1 anon ->
        anon = f x /\
        (forall x2 : int, hmem x2 t1 = true -> hget x2 t1 = f x2))).
     Proof.
       unfold myfun; simpl; intuition.
      Qed.
     
      Lemma goal3: fst anon3 x6 t4.
        Proof.
          fold myfun in *.
          generalize (proj2 (H myfun K) anon3 H5); clear H; intuition.
        apply (proj1 (H x6 t4 H1)).
       Qed.
        
      Section sec5.
         Variable t11:  hmap Z Z. 
        Variable anon4:  Z. 
        Hypothesis H6: snd anon3 x6 t4 t11 anon4. 
        Lemma goal4: anon4 = (f x6).
          Proof.
            fold myfun in *.
          generalize (proj2 (H myfun K) anon3 H5); clear H; intuition.
          apply ((proj2 (H x6 t4 H1)) t11 anon4). auto.
        Qed.
          
        Section sec6.
           Variable x17:  Z. 
          Hypothesis H7: (hmem x17 (hset x6 anon4 t11)) = true. 
          Lemma goal5:
            (hget x17 (hset x6 anon4 t11)) = (f x17).
            Proof.
              fold myfun in *.
              generalize (proj2 (H myfun K) anon3 H5); clear H; intuition.
              generalize (H x6 t4 H1); clear H; intuition.
              generalize (H2 t11 anon4 H6); clear H2; intuition.
              case_eq (Z_eq_dec x17 x6); intros A _.
              subst. rewrite hgethset; auto.
              rewrite hgethset1; auto.
              apply H3. 
              assert (x17 = x6 \/ hmem x17 t11 = true).
              apply set_mem with anon4; auto.
              intuition.
            Qed.
             End sec6. End sec5. End sec4. End sec3. End sec.