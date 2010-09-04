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

Definition mmod:  Z -> Z -> Z.
  Proof.
  Admitted.
   
Hypothesis mmod1:
  forall (a:Z), forall (b:Z), (0 <= (mmod a b)) /\ ((mmod a b) < b). 
Definition hashkey : Type. 
  Proof.
  Admitted.
   
Definition hash:  hashkey -> Z.
  Proof.
  Admitted.
   
Definition repr: forall (a : Type) ,  (array (list (hashkey * a))) ->
  (list (hashkey * a)) -> Prop.
  Proof.
  Admitted.
   
Section sec. 
   Variables a r : Type.
  
  Variable l:  list (hashkey * a). 
  Variable h:  refty r (array (list (hashkey * a))). 
  Variable key:  hashkey. 
  Variable val:  a. 
  Variable s:  region r. 
  Hypothesis H:
    0 <
    ((@len  (list (hashkey * a)))
     ((@ref_get  r (array (list (hashkey * a)))) s h)). 
  Hypothesis H1:
    forall (i:Z),
    (0 <= i) ->
    ((i <
      ((@len  (list (hashkey * a)))
       ((@ref_get  r (array (list (hashkey * a)))) s h)))
     ->
     (forall (k:hashkey),
      forall (v:a),
      ((@l_in  (hashkey * a)) ((@mk_2tuple  hashkey a) k v)
       ((@get  (list (hashkey * a))) i
        ((@ref_get  r (array (list (hashkey * a)))) s h)))
      ->
      (i =
       (mmod (hash k)
        ((@len  (list (hashkey * a)))
         ((@ref_get  r (array (list (hashkey * a)))) s h)))))). 
  Variable s1:  region r. 
  Hypothesis H2:
    ((@set  (list (hashkey * a)))
     (mmod (hash key)
      ((@len  (list (hashkey * a)))
       ((@ref_get  r (array (list (hashkey * a)))) s h)))
     ((@Cons  (hashkey * a)) ((@mk_2tuple  hashkey a) key val)
      ((@get  (list (hashkey * a)))
       (mmod (hash key)
        ((@len  (list (hashkey * a)))
         ((@ref_get  r (array (list (hashkey * a)))) s h)))
       ((@ref_get  r (array (list (hashkey * a)))) s h)))
     ((@ref_get  r (array (list (hashkey * a)))) s h))
    = ((@ref_get  r (array (list (hashkey * a)))) s1 h). 
  Lemma add_correct:
    0 <
    ((@len  (list (hashkey * a)))
     ((@ref_get  r (array (list (hashkey * a)))) s1 h)). 
    Proof.
      rewrite <- H2. rewrite <- update_len; auto. apply mmod1.
    Qed.
     End sec.
