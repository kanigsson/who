Set Implicit Arguments.



Definition region : forall (u : Type) , Type. 
  Proof.
  Admitted.
   
Definition refty : forall (reg ty : Type) , Type. 
  Proof.
  Admitted.
   
Definition ref_get: forall (reg u : Type) ,  (region reg) -> (refty reg u) ->
  u.
  Proof.
  Admitted.
   
Require Import WhoTuples.
Require Import WhoArith.

Require Import WhoMap.
Require Import WhoArray.
Require Import WhoList.

Section sec. 
   Variables a b e : Type.
  
  Variable ia:  e -> (list a) -> Prop. 
  Variable ib:  (list b) -> Prop. 
  Variable f_pre:  a -> e -> Prop. 
  Variable f_post:  a -> e -> e -> b -> Prop. 
  Variable l:  list a. 
  Variable s:  e. 
  Hypothesis H: ia s l. 
  Hypothesis H1: ib (@Nil  b). 
  Hypothesis H2:
    forall (x:a),
    forall (l1:list a),
    forall (k:list b),
    forall (s1:e),
    (ia s1 ((@Cons  a) x l1)) ->
    ((ib k) ->
     ((f_pre x s1) /\
      (forall (s2:e),
       forall (anon:b),
       (f_post x s1 s2 anon) -> ((ia s2 l1) /\ (ib ((@Cons  b) anon k)))))). 
  Lemma map_correct:
    match l with nil =>  (ia s (@Nil  a)) /\ (ib (@Nil  b))  | Cons x rl =>
                  (f_pre x s) /\
                  (forall (s1:e),
                   forall (anon:b),
                   (f_post x s s1 anon) ->
                   ((((ia s1 rl) /\ (ib (@Nil  b))) /\
                     (forall (x1:a),
                      forall (l1:list a),
                      forall (k:list b),
                      forall (s2:e),
                      (ia s2 ((@Cons  a) x1 l1)) ->
                      ((ib k) ->
                       ((f_pre x1 s2) /\
                        (forall (s3:e),
                         forall (anon1:b),
                         (f_post x1 s2 s3 anon1) ->
                         ((ia s3 l1) /\ (ib ((@Cons  b) anon1 k))))))))
                    /\
                    (forall (s2:e),
                     forall (anon1:list b),
                     (ia s2 (@Nil  a)) ->
                     ((ib anon1) ->
                      ((ia s2 (@Nil  a)) /\ (ib ((@Cons  b) anon anon1)))))))  end . 
    Proof.
      destruct l; intuition.
      generalize (H2 H H1); clear H2; intros [ A B]. auto.
      generalize (H2 H H1); clear H2; intros [ A B]. 
      apply (B s1 anon H0).
      generalize (H2 H H4); clear H2; intros [ A B].
      apply (B s1 anon H0).
    Qed.
      
     End sec.
