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
  (*whoArra*) Require Import WhoArray. (*who*) 
  (*whoLis*) Require Import WhoList. (*who*) 
  (*whomap*) Definition map : forall (a b : Type)  , Type.  (*who*) Admitted.
  (*whomem*) Definition mem: forall (a1 b1 : Type)  , a1 -> (map a1 b1) ->
               bool.  (*who*) Admitted.
  (*whoget*) Definition get: forall (a2 b2 : Type)  , a2 -> (map a2 b2) ->
               b2.  (*who*) Admitted.
  (*whoset*) Definition set: forall (a3 b3 : Type)  , a3 -> b3 -> (map a3
               b3) -> map a3 b3.  (*who*) Admitted.(*whot*) Variables t :
  key.  (*who*) (*whotable*) Variable table: ref (map int int) t.  (*who*) 
  (*whof0*) Variable f0: int -> int.  (*who*) 
  (*whof*) Variable f: (int -> kmap -> Prop) * (int -> kmap -> kmap -> int ->
             Prop).  (*who*) (*whos*) Variable s: kmap.  (*who*) 
  (*whox*) Variable x: int.  (*who*) 
  (*whoH*) Hypothesis H: fst f x empty.  (*who*) 
  (*whoH1*) Hypothesis H1:
            forall (x1:int),
            ((mem x1 (!! table s)) = true) ->
            ((get x1 (!! table s)) = (f0 x1)).  (*who*) 
  (*whos1*) Variable s1: kmap.  (*who*) 
  (*whoH2*) Hypothesis H2: (!! table s) = (!! table s1).  (*who*) 
  
  (*whobeginsec1*)
  Section sec1. (*who*)
    (*whoH3*) Hypothesis H3: (mem x (!! table s1)) = true.  (*who*) 
    (*whos2*) Variable s2: kmap.  (*who*) 
    (*whoH4*) Hypothesis H4: (!! table s1) = (!! table s2).  (*who*) 
    (*whogoal*) Lemma goal: (get x (!! table s2)) = (f0 x). (*who*) 
    Proof.
    (*whoendsec1*)
    End sec1. (*who*)
  
  (*whobeginsec2*)
  Section sec2. (*who*)
    (*whoH5*) Hypothesis H5: ~ ((mem x (!! table s1)) = true).  (*who*) 
    (*whogoal1*) Lemma goal1: fst f x (restrict s1). (*who*) 
    
    (*whobeginsec3*)
    Section sec3. (*who*)
      (*whoanon*) Variable anon: int.  (*who*) 
      (*whoH6*) Hypothesis H6: snd f x (restrict s1) empty anon.  (*who*) 
      (*whos3*) Variable s3: kmap.  (*who*) 
      (*whoH7*) Hypothesis H7: (!! table s1) = (!! table s3).  (*who*) 
      (*whos4*) Variable s4: kmap.  (*who*) 
      (*whoH8*) Hypothesis H8: (!! table s4) = (set x anon (!! table s3)).  (*who*) 
      (*whogoal2*) Lemma goal2: anon = (f0 x). (*who*) 
      (*whoendsec3*)
      End sec3. (*who*)
    
    (*whoendsec2*)
    End sec2. (*who*)
  
  (*whoendsec*)
  End sec. (*who*)
