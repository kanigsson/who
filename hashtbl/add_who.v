(*whoSet*) Set Implicit Arguments. (*who*) 
(*whoRequire*) Require Import WhoMap. (*who*) 
(*whoVariable*) Variable ref : forall (a : Type) (k : key), Type. (*who*) 
(*whoDefinition*) Definition ___get (A : Type) (k : key) (r : ref A k) (m : kmap) :=
        __get A k m. (*who*) 
(*whoNotation*) Notation "!!" := (___get) (at level 50). (*who*) 

(*whobeginsec*)
Section sec. (*who*)
  (*whobasiclogi*)  (*who*) (*whoarit*) Require Import WhoArith. (*who*) 
  (*whocombine*) Definition combine: forall   (e1 e2 : kmap), kmap -> kmap ->
                   kmap.  (*who*) Admitted.
  (*whorestrict*) Definition restrict: forall   (e11 e21 : kmap), kmap ->
                    kmap.  (*who*) Admitted.
  (*whoLis*) Require Import WhoList. (*who*) 
  (*whoArra*) Require Import WhoArray. (*who*) 
  (*whohashkey*) Definition hashkey : Type.  (*who*) Admitted.
  (*whohash*) Definition hash: hashkey -> int.  (*who*) 
  Admitted.
  (*whorepr*) Definition repr: forall (b : Type)  , (array (list (hashkey *
                b))) -> (list (hashkey * b)) -> Prop.  (*who*) 
  Admitted.
  (*whoa*) Variables a : Type. Variables r : key.  (*who*) 
  (*whol*) Variable l: list (hashkey * a).  (*who*) 
  (*whoh*) Variable h: ref (array (list (hashkey * a))) r.  (*who*) 
  (*whokey*) Variable key: hashkey.  (*who*) 
  (*whos*) Variable s: kmap.  (*who*) (*whoval*) Variable val: a.  (*who*) 
  (*whoH*) Hypothesis H: 0 < (length (!! h s)).  (*who*) 
  (*whoH1*) Hypothesis H1:
            forall (i1:int),
            (0 <= i1) ->
            ((i1 < (length (!! h s))) ->
             (forall (k1:hashkey),
              forall (v1:a),
              (l_in (k1 , v1) (get i1 (!! h s))) ->
              ((mod (hash k1) (length (!! h s))) = i1))).  (*who*) 
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
            (set (mod (hash key) (length (!! h s1)))
             (cons (key , val)
              (get (mod (hash key) (length (!! h s1))) (!! h s2)))
             (!! h s3)).  (*who*) 
  (*whogoal*) Lemma goal: 0 < (length (!! h s4)). (*who*) 
  Proof.  rewrite H6, <- update_length, <- H5, <- H4, <- H3. auto. Qed.
  (*whobeginsec1*)
  Section sec1. (*who*)
    (*whoi*) Variable i: int.  (*who*) 
    (*whoH7*) Hypothesis H7: 0 <= i.  (*who*) 
    (*whoH8*) Hypothesis H8: i < (length (!! h s4)).  (*who*) 
    (*whok*) Variable k: hashkey.  (*who*) (*whov*) Variable v: a.  (*who*) 
    (*whoH9*) Hypothesis H9: l_in (k , v) (get i (!! h s4)).  (*who*) 
    (*whogoal1*) Lemma goal1: (mod (hash k) (length (!! h s4))) = i. (*who*) 
    Proof.
      rewrite H6, H3, H4, H5 in *|-*; rewrite <- update_length in *|-*; clear H6 H5 H4 H3.
      case_eq (Z_eq_dec i (mod (hash key) (length (!! h s3)))); intros; auto.
      rewrite <- e, get_set_eq in H9; auto. 
      generalize (in_inv H9); intros [K|K]. clear H0.
      injection K; intros K1 K2; rewrite K1, K2 in *; clear K1 K2 K; auto.
      apply H1 with v; auto.
      rewrite get_set_neq in H9; auto.
      apply H1 with v; auto. admit.
    Qed.
    (*whoendsec1*)
    End sec1. (*who*)
  (*whogoal2*) Lemma goal2: repr (!! h s4) (cons (key , val) l). (*who*) 
  
  (*whoendsec*)
  End sec. (*who*)
