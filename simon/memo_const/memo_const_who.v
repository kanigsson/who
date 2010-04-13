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

Require Import Bool.

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
   
Definition fromSome: forall (a : Type) ,  (option a) -> a.
  Proof.
  Admitted.
   
Hypothesis fromSome_ax: forall (a : Type) ,
   forall (v:a), v = (fromSome (Some v)). 
Section sec. 
   Variables a : Type.
  
  Variable arg:  a. 
  Variable s:  region t. 
  Hypothesis H:
    ((ref_get s res) <> (@None  u)) ->
    (forall (x:a), (ref_get s res) = (Some (f x))). 
  Section sec1. 
     Hypothesis H1: (@None  u) = (ref_get s res). 
    Variables t' : Type.
    
    Variable s1:  region t'. 
    Variable s2:  region t'. 
    Variable anon:  refty t' bool. 
    Hypothesis H2: false = (ref_get s2 anon). 
    Lemma goal:
      exists const:a,
      forall (s3:region t'),
      forall (s4:region t'), (true = (ref_get s4 anon)) -> (arg = const). 
      Proof.
      Admitted.
      
    Section sec2. 
       Variable s3:  region t'. 
      Variable anon1:  u. 
      Hypothesis H3:
        exists const:a,
        ((forall (s4:region t'),
          forall (s5:region t'), (true = (ref_get s5 anon)) -> (arg = const))
         /\ (anon1 = (f const)))
        /\
        ((forall (x:a), anon1 = (f x)) \/
         (exists s4:region t',
          exists c:a,
          ((arg = c) /\ (true = (ref_get s3 anon))) /\ (anon1 = (f c)))). 
      Section sec3. 
         Hypothesis H4: true = (ref_get s3 anon). 
        Lemma goal1: anon1 = (f arg). 
          Proof.
          Admitted.
          
        Section sec4. 
           Hypothesis H5: (ref_get s res) <> (@None  u). 
          Variable x:  a. 
          Lemma goal2: (ref_get s res) = (Some (f x)). 
            Proof.
            Admitted.
             End sec4. End sec3.




      Section sec5. 
         Hypothesis H6: false = (ref_get s3 anon). 
        Variable s4:  region t. 
        Hypothesis H7: (Some anon1) = (ref_get s4 res). 
        Lemma goal3: anon1 = (f arg). 
          Proof.
          elim H3. clear H3.
          intros.
          decompose [and or] H0; clear H0.
            apply (H3 arg).

            decompose [ex] H3.
            decompose [and] H4. clear H3 H4.
            rewrite <- H10 in H9.
            assumption.
            Qed.
            

            
          
          
        Section sec6. 
           Hypothesis H8: (ref_get s4 res) <> (@None  u). 
          Variable x1:  a. 
          Lemma goal4: (ref_get s4 res) = (Some (f x1)). 
            Proof.
            rewrite <- H7.
            apply f_equal.
            elim H3. clear H3.
            intros.
            decompose [and or] H0; clear H0.
              apply (H3 x1).

              decompose [ex] H3. clear H3.
              decompose [and] H4. clear H4.
              contradict H6.
              rewrite <- H11.
              apply diff_false_true.
            Qed.
            
            
             

           End sec6. End sec5. End sec2. End sec1.







  Section sec7. 
     Hypothesis H9: ~ ((@None  u) = (ref_get s res)). 
    Lemma goal5: (fromSome (ref_get s res)) = (f arg). 
      Proof.
      apply sym_not_eq in H9.
      specialize ((H H9) arg).
      

      

      
      
    Section sec8. 
       Hypothesis H10: (ref_get s res) <> (@None  u). 
      Variable x2:  a. 
      Lemma goal6: (ref_get s res) = (Some (f x2)). 
        Proof.
        Admitted.
         End sec8. End sec7. End sec.
Section sec9. 
   Variable s5:  region t. 
  Hypothesis H11: (@None  u) = (ref_get s5 res). 
  Hypothesis H12: (ref_get s5 res) <> (@None  u). 
  Variable x3:  Z. 
  Lemma main_correct: (ref_get s5 res) = (Some (f x3)). 
    Proof.
    Admitted.
     End sec9.
