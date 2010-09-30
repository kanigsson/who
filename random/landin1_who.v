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

Variables r : Type.

Section sec. 
   Variables a : Type.
  
  Variable p:  ((a -> (region r) -> Prop) * (a -> (region r) -> (region r) ->
    a -> Prop)) -> (region r) -> Prop. 
  Variable f_pre:  (refty r ((a -> (region r) -> Prop) * (a -> (region r) ->
    (region r) -> a -> Prop))) -> unit -> Prop. 
  Variable f_post:  (refty r ((a -> (region r) -> Prop) * (a -> (region r) ->
    (region r) -> a -> Prop))) -> unit -> unit -> ((a -> (region r) ->
    Prop) * (a -> (region r) -> (region r) -> a -> Prop)) -> Prop. 
  Variable s:  region r. 
  Hypothesis H:
    forall (x:refty r ((a -> (region r) -> Prop) * (a -> (region r) ->
    (region r) -> a -> Prop))),
    (f_pre x tt) /\
    (forall (anon_pre:a -> (region r) -> Prop),
     forall (anon_post:a -> (region r) -> (region r) -> a -> Prop),
     (f_post x tt tt
      ((@mk_2tuple  (a -> (region r) -> Prop) (a -> (region r) ->
       (region r) -> a -> Prop)) anon_pre anon_post))
     ->
     (forall (s1:region r),
      (p
       ((@ref_get  r ((a -> (region r) -> Prop) * (a -> (region r) ->
        (region r) -> a -> Prop))) s1 x)
       s1)
      ->
      (p
       ((@mk_2tuple  (a -> (region r) -> Prop) (a -> (region r) ->
        (region r) -> a -> Prop)) anon_pre anon_post)
       s1))). 
  Variable s1:  region r. 
  Variable anon:  refty r ((a -> (region r) -> Prop) * (a -> (region r) ->
    (region r) -> a -> Prop)). 
  Hypothesis H1:
    ((@mk_2tuple  (a -> (region r) -> Prop) (a -> (region r) -> (region r) ->
     a -> Prop)) (fun (x:a) => (fun (cur:region r) => True))
     (fun (x:a) =>
     (fun (old:region r) => (fun (cur:region r) => (fun (anon1:a) => True)))))
    =
    ((@ref_get  r ((a -> (region r) -> Prop) * (a -> (region r) ->
     (region r) -> a -> Prop))) s1 anon). 
  Variable anon_pre:  a -> (region r) -> Prop. 
  Variable anon_post:  a -> (region r) -> (region r) -> a -> Prop. 
  Hypothesis H2:
    f_post anon tt tt
    ((@mk_2tuple  (a -> (region r) -> Prop) (a -> (region r) -> (region r) ->
     a -> Prop)) anon_pre anon_post). 
  Variable s2:  region r. 
  Hypothesis H3:
    ((@mk_2tuple  (a -> (region r) -> Prop) (a -> (region r) -> (region r) ->
     a -> Prop)) anon_pre anon_post)
    =
    ((@ref_get  r ((a -> (region r) -> Prop) * (a -> (region r) ->
     (region r) -> a -> Prop))) s2 anon). 
  Lemma backpatch_correct:
    p
    ((@ref_get  r ((a -> (region r) -> Prop) * (a -> (region r) ->
     (region r) -> a -> Prop))) s2 anon)
    s2. 
    Proof.
      rewrite <- H3 in *; clear H3.
      generalize (H anon); clear H. intuition.
      apply H3; auto.
    Qed.
     End sec.
