(*whoSet*) Set Implicit Arguments. (*who*) 

(*whobeginsec*)
Section sec. (*who*)
  (*whobasiclogi*)  (*who*) (*whoarit*) Require Import WhoArith. (*who*) 
  (*whoWhore*) Require Import WhoRef. (*who*) 
  (*whoArra*) Require Import WhoArray. (*who*) 
  (*whoLis*) Require Import WhoList. (*who*) 
  (*whohmap*) Definition hmap : forall (a b : Type)  , Type.  (*who*) 
  Admitted.
  (*whohmem*) Definition hmem: forall (a1 b1 : Type)  , a1 -> (hmap a1 b1) ->
                bool.  (*who*) Admitted.
  (*whohget*) Definition hget: forall (a2 b2 : Type)  , a2 -> (hmap a2 b2) ->
                b2.  (*who*) Admitted.
  (*whohset*) Definition hset: forall (a3 b3 : Type)  , a3 -> b3 -> (hmap a3
                b3) -> hmap a3 b3.  (*who*) Admitted.
 (*whot*) Variables t :
  key.  (*who*) (*whot1*) Variable t1: key.  (*who*) 
  (*whotable*) Variable table: ref (hmap int int) t.  (*who*) 
  (*whof0*) Variable f0: int -> int.  (*who*) 
  (*whot2*) Variable t2: hmap int int.  (*who*) 
  (*whox*) Variable x: int.  (*who*) 
  (*whoH*) Hypothesis H:
           forall (x3:int), ((hmem x3 t2) = true) -> ((hget x3 t2) = (f0 x3)).  (*who*) 
  (*whot3*) Variable t3: hmap int int.  (*who*) 
  (*whoH1*) Hypothesis H1: t2 = t3.  (*who*) 
  
  (*whobeginsec1*)
  Section sec1. (*who*)
    (*whoH2*) Hypothesis H2: (hmem x t3) = true.  (*who*) 
    (*whot4*) Variable t4: hmap int int.  (*who*) 
    (*whoH3*) Hypothesis H3: t3 = t4.  (*who*) 
    (*whogoal*) Lemma goal: (hget x t4) = (f0 x). (*who*) 
      Proof. subst; auto. Qed.
    
    (*whobeginsec2*)
    Section sec2. (*who*)
      (*whox1*) Variable x1: int.  (*who*) 
      (*whoH4*) Hypothesis H4: (hmem x1 t4) = true.  (*who*) 
      (*whogoal1*) Lemma goal1: (hget x1 t4) = (f0 x1). (*who*) 
      
      (*whoendsec2*)
      End sec2. (*who*)
    
    (*whoendsec1*)
    End sec1. (*who*)
  
  (*whobeginsec3*)
  Section sec3. (*who*)
    (*whoH5*) Hypothesis H5: ~ ((hmem x t3) = true).  (*who*) 
    Proof. auto. Qed.(*whot5*) Variable t5: hmap int int.  (*who*) 
    (*whoH6*) Hypothesis H6: t3 = t5.  (*who*) 
    (*whot6*) Variable t6: hmap int int.  (*who*) 
    (*whoH7*) Hypothesis H7: t6 = (hset x (f0 x) t5).  (*who*) 
    (*whox2*) Variable x2: int.  (*who*) 
    (*whoH8*) Hypothesis H8: (hmem x2 t6) = true.  (*who*) 
    (*whogoal2*) Lemma goal2: (hget x2 t6) = (f0 x2). (*who*) 
    Proof.
    (*whoendsec3*)
    End sec3. (*who*)
  
  (*whoendsec*)
  End sec. (*who*)
