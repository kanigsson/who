(*whoSet*) Set Implicit Arguments. (*who*) 
(*whoRequire*) Require Import WhoMap. (*who*) 
(*whoRequire1*) Require Import ZArith. (*who*) 
(*whoOpen*) Open Scope Z_scope. (*who*) 
(*whoRequire2*) Require Omega. (*who*) 
(*whoVariable*) Variable ref : forall (a : Type) (k : key), Type. (*who*) 
(*whoDefinition*) Definition ___get (A : Type) (k : key) (r : ref A k) (m : kmap) :=
        __get A k m. (*who*) 
(*whoNotation*) Notation "!!" := (___get) (at level 50). (*who*) 
(*whoDefinition1*) Definition min := Zmin. (*who*) 
(*whoNotation1*) Notation max := Zmax. (*who*) 
Require Import List.
(*whobeginsec*)
Section sec. (*who*)
  
  (*whocombine*) Definition combine: forall   (e1 e2 : kmap), kmap -> kmap ->
                   kmap.  (*who*) Admitted.
  (*whorestrict*) Definition restrict: forall   (e11 e21 : kmap), kmap ->
                    kmap.  (*who*) Admitted.
  (*whoarray*) Definition array : forall (a : Type)  , Type.  (*who*) 
  Admitted.
  (*whoget*) Definition get: forall (a1 : Type)  , Z -> (array a1) -> a1.  (*who*) 
  Admitted.
  (*whoset*) Definition set: forall (a2 : Type)  , Z -> a2 -> (array a2) ->
               array a2.  (*who*) Admitted.
  (*wholength*) Definition length: forall (a3 : Type)  , (array a3) -> Z.  (*who*) 
  Admitted.
  (*whoupdate_length*) Axiom update_length: forall (a4 : Type)  ,
                        forall (t:array a4),
                        forall (i:Z),
                        forall (z:a4), (length t) = (length (set i z t)).  (*who*) 
  
  (*whoget_set_eq*) Axiom get_set_eq: forall (a5 : Type)  ,
                     forall (t1:array a5),
                     forall (i1:Z),
                     forall (z1:a5),
                     (i1 < (length t1)) -> ((get i1 (set i1 z1 t1)) = z1).  (*who*) 
  
  (*whoget_set_neq*) Axiom get_set_neq: forall (a6 : Type)  ,
                      forall (t2:array a6),
                      forall (i2:Z),
                      forall (j:Z),
                      forall (z2:a6),
                      (i2 < (length t2)) ->
                      ((j < (length t2)) ->
                       ((i2 <> j) -> ((get i2 (set j z2 t2)) = (get i2 t2)))).  (*who*) 
  
  (*wholength_nonnegative*) Axiom length_nonnegative: forall (a7 : Type)  ,
                             forall (t3:array a7), 0 <= (length t3).  (*who*) 
  (*whomlist*) Definition mlist : forall (a8 : Type)  , Type.  (*who*) 
  exact list. Defined.
  (*whomnil*) Definition mnil: forall (a9 : Type)  , mlist a9.  (*who*) 
  intros a; exact nil. Defined.
  (*whomcons*) Definition mcons: forall (a10 : Type)  , a10 -> (mlist a10) ->
                 mlist a10.  (*who*) exact cons. Defined.
  (*whomis_nil*) Definition mis_nil: forall (a11 : Type)  , (mlist a11) ->
                   bool.  (*who*) 
  intros a l; exact (match l with nil => true | cons _ _ => false end). Defined.
  (*whommem*) Definition mmem: forall (a12 : Type)  , a12 -> (mlist a12) ->
                Prop.  (*who*) exact In. Defined.
  (*whohashkey*) Definition hashkey : Type.  (*who*) 
  (*whohash*) Definition hash: hashkey -> Z.  (*who*) 
  Admitted.
  Hint Unfold mlist mnil mcons mis_nil mmem.
  (*whorepr*) Definition repr: forall (b : Type)  , (array (mlist (hashkey *
                b))) -> (mlist (hashkey * b)) -> Prop.  (*who*) 
  (*whoa13*) Variables a13 : Type. Variables r : key.  (*who*) 
  (*whol*) Variable l: mlist (hashkey * a13).  (*who*) 
  (*whoh*) Variable h: ref (array (mlist (hashkey * a13))) r.  (*who*) 
  (*whokey*) Variable key: hashkey.  (*who*) 
  (*whos*) Variable s: kmap.  (*who*) (*whoval*) Variable val: a13.  (*who*) 
  (*whoH*) Hypothesis H: 0 < (length (!! h s)).  (*who*) 
  (*whoH1*) Hypothesis H1:
            forall (i3:Z),
            (0 <= i3) ->
            ((i3 < (length (!! h s))) ->
             (forall (k:hashkey),
              forall (v:a13),
              (mmem (k , v) (get i3 (!! h s))) ->
              ((Zmod (hash k) (length (!! h s))) = i3))).  (*who*) 
  (*whoH2*) Hypothesis H2: repr (!! h s) l.  (*who*) 
  (*whos1*) Variable s1: kmap.  (*who*) 
  (*whoH3*) Hypothesis H3: (!! h s) = (!! h s1).  (*who*) 
  (*whos2*) Variable s2: kmap.  (*who*) 
  (*whoH4*) Hypothesis H4: (!! h s1) = (!! h s2).  (*who*) 
  (*whos3*) Variable s3: kmap.  (*who*) 
  (*whoH5*) Hypothesis H5: (!! h s2) = (!! h s3).  (*who*) 
  (*whos4*) Variable s4: kmap.  (*who*) 
  (*whoH6*) Hypothesis H6:
            (!! h s4) =
            (set (Zmod (hash key) (length (!! h s1)))
             (mcons (key , val)
              (get (Zmod (hash key) (length (!! h s1))) (!! h s2)))
             (!! h s3)).  (*who*) 
  (*whogoal*) Lemma goal: 0 < (length (!! h s4)). (*who*) 
  Proof.  rewrite H5, <- update_length, <- H4, <- H3, <- H2. auto. Qed.
  (*whobeginsec1*)
  Section sec1. (*who*)
    (*whoi4*) Variable i4: Z.  (*who*) 
    (*whoH7*) Hypothesis H7: 0 <= i4.  (*who*) 
    (*whoH8*) Hypothesis H8: i4 < (length (!! h s4)).  (*who*) 
    (*whok1*) Variable k1: hashkey.  (*who*) 
    (*whov1*) Variable v1: a13.  (*who*) 
    (*whoH9*) Hypothesis H9: mmem (k1 , v1) (get i4 (!! h s4)).  (*who*) 
    (*whogoal1*) Lemma goal1: (Zmod (hash k1) (length (!! h s4))) = i4. (*who*) 
    Proof.
      rewrite H5, H2, H3, H4 in *|-*; rewrite <- update_length in *|-*; clear H5 H4 H3 H2.
      case_eq (Z_eq_dec i3 (hash key mod length (!! h s3))); intros; auto.
      rewrite <- e, get_set_eq in H8; auto. 
      generalize (in_inv H8); intros [K|K]. clear H0.
      injection K; intros K1 K2; rewrite K1, K2 in *; clear K1 K2 K; auto.
      apply H1 with v; auto.
      rewrite get_set_neq in H8; auto.
      apply H1 with v; auto. admit.
    Qed.
    (*whoendsec1*)
    End sec1. (*who*)
  (*whogoal2*) Lemma goal2: repr (!! h s4) (mcons (key , val) l). (*who*) 
  
  (*whoendsec*)
  End sec. (*who*)
