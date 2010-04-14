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

Variables t : Type.

Definition u : Type. 
  Proof.
  Admitted.
   
Definition res:  refty t (option u).
  Proof.
  Admitted.
   
Definition f: forall (a : Type) ,  a -> u.
  Proof.
  Admitted.
   
Section sec. 
   Variables a : Type.
  
  Variable arg:  a. 
  Variable s:  region t. 
  Hypothesis H: (@None  u) = (ref_get s res). 
  Hypothesis H1:
    ((ref_get s res) <> (@None  u)) ->
    (forall (x:a), (ref_get s res) = (Some (f x))). 
  Variables t' : Type.
  
  Variable s1:  region t'. 
  Variable s2:  region t'. 
  Variable anon:  refty t' bool. 
  Hypothesis H2: false = (ref_get s2 anon). 
  Lemma memo_const_correct:
    exists const:a,
    forall (s3:region t'),
    forall (s4:region t'), (true = (ref_get s4 anon)) -> (arg = const). 
    Proof.
    exists arg.
    intros.
    auto.
    Qed.

End sec.
