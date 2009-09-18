(*whoSet*) Set Implicit Arguments. (*who*) 
(*whoRequire*) Require Import WhoMap. (*who*) 
(*whoRequire1*) Require Import ZArith. (*who*) 
(*whoOpen*) Open Scope Z_scope. (*who*) 
(*whoRequire2*) Require Omega. (*who*) 
(*whoVariable*) Variable ref : forall (a : Set) (k : key), Set. (*who*) 
(*whoDefinition*) Definition ___get (A : Set) (k : key) (r : ref A k) (m : kmap) :=
        __get A k m. (*who*) 
(*whoNotation*) Notation "!!" := (___get) (at level 50). (*who*) 
(*whoDefinition1*) Definition min := Zmin. (*who*) 
(*whoNotation1*) Notation max := Zmax. (*who*) 

(*whobeginsec*)
Section sec. (*who*)
  (*whocombine*) Variable combine: forall   (e1 e2 : kmap), kmap -> kmap ->
                   kmap.  (*who*) 
  (*whorestrict*) Variable restrict: forall   (e11 e21 : kmap), kmap ->
                    kmap.  (*who*) 
  (*whoarray*) Parameter array : forall (a : Set)  , Set.  (*who*) 
  (*whoget*) Variable get: forall (a1 : Set)  , Z -> (array a1) -> a1.  (*who*) 
  (*whoset*) Variable set: forall (a2 : Set)  , Z -> a2 -> (array a2) ->
               array a2.  (*who*) 
  (*wholength*) Variable length: forall (a3 : Set)  , (array a3) -> Z.  (*who*) 
  (*whoupdate_length*) Axiom update_length: forall (a4 : Set)  ,
                        forall (t:array a4),
                        forall (i:Z),
                        forall (z:a4), (length t) = (length (set i z t)).  (*who*) 
  (*whoget_set_eq*) Axiom get_set_eq: forall (a5 : Set)  ,
                     forall (t1:array a5),
                     forall (i1:Z),
                     forall (z1:a5),
                     (i1 < (length t1)) -> ((get i1 (set i1 z1 t1)) = z1).  (*who*) 
  (*whoget_set_neq*) Axiom get_set_neq: forall (a6 : Set)  ,
                      forall (t2:array a6),
                      forall (i2:Z),
                      forall (j:Z),
                      forall (z2:a6),
                      (i2 < (length t2)) ->
                      ((j < (length t2)) ->
                       ((i2 <> j) -> ((get i2 (set j z2 t2)) = (get i2 t2)))).  (*who*) 
  (*wholength_nonnegative*) Axiom length_nonnegative: forall (a7 : Set)  ,
                             forall (t3:array a7), 0 <= (length t3).  (*who*) 
  (*whoa8*) Variables a8 : Set. Variables r1 r2 : key.  (*who*) 
  (*whoar1*) Variable ar1: ref (array a8) r1.  (*who*) 
  (*whoar2*) Variable ar2: ref (array a8) r2.  (*who*) 
  (*whoofs1*) Variable ofs1: Z.  (*who*) 
  (*whoofs2*) Variable ofs2: Z.  (*who*) 
  (*whoanon*) Variable anon: kmap.  (*who*) 
  (*wholen*) Variable len: Z.  (*who*) 
  (*whoH*) Hypothesis H: 0 <= len.  (*who*) 
  (*whoH1*) Hypothesis H1: 0 <= ofs1.  (*who*) 
  (*whoH2*) Hypothesis H2: 0 <= ofs2.  (*who*) 
  (*whoH3*) Hypothesis H3: ofs1 <= ((length (!! ar1 anon)) - len).  (*who*) 
  (*whoH4*) Hypothesis H4: ofs2 <= ((length (!! ar2 anon)) - len).  (*who*) 
  (*whoanon1*) Variable anon1: kmap.  (*who*) 
  (*whoH5*) Hypothesis H5: (!! ar1 anon) = (!! ar1 anon1).  (*who*) 
  (*whoanon2*) Variable anon2: kmap.  (*who*) 
  (*whoH6*) Hypothesis H6: (!! ar2 anon) = (!! ar2 anon2).  (*who*) 
  
  (*whobeginsec1*)
  Section sec1. (*who*)
    (*whoH7*) Hypothesis H7: ofs1 < ofs2.  (*who*) 
    
    (*whobeginsec2*)
    Section sec2. (*who*)
      (*whoanon3*) Variable anon3: kmap.  (*who*) 
      (*whoi3*) Variable i3: Z.  (*who*) 
      (*whoH8*) Hypothesis H8: (len - 1) <= i3.  (*who*) 
      (*whoH9*) Hypothesis H9: i3 <= 0.  (*who*) 
      (*whoH10*) Hypothesis H10: (!! ar1 anon3) = (!! ar1 anon1).  (*who*) 
      (*whoH11*) Hypothesis H11:
                 (length (!! ar2 anon3)) = (length (!! ar2 anon2)).  (*who*) 
      (*whoH12*) Hypothesis H12:
                 forall (k:Z),
                 (i3 < k) ->
                 ((k <= (len - 1)) ->
                  ((get (ofs2 + k) (!! ar2 anon3)) =
                   (get (ofs1 + k) (!! ar1 anon3)))).  (*who*) 
      (*whoanon4*) Variable anon4: kmap.  (*who*) 
      (*whoH13*) Hypothesis H13: (!! ar1 anon3) = (!! ar1 anon4).  (*who*) 
      (*whoanon5*) Variable anon5: kmap.  (*who*) 
      (*whoH14*) Hypothesis H14: (!! ar2 anon3) = (!! ar2 anon5).  (*who*) 
      (*whoanon6*) Variable anon6: kmap.  (*who*) 
      (*whoH15*) Hypothesis H15:
                 (!! ar2 anon6) =
                 (set (ofs2 + i3) (get (ofs1 + i3) (!! ar1 anon4))
                  (!! ar2 anon5)).  (*who*) 
      (*whogoal*) Lemma goal: (!! ar1 anon4) = (!! ar1 anon1). (*who*) 
      Proof. transitivity (!! ar1 anon3); auto. Qed.
        
      (*whogoal1*) 
      Lemma goal1: (length (!! ar2 anon6)) = (length (!! ar2 anon2)). (*who*) 
      Proof. rewrite H15, <- update_length, <- H14; auto. Qed.
      
      
      
      (*whobeginsec3*)
      Section sec3. (*who*)
        (*whok1*) Variable k1: Z.  (*who*) 
        (*whoH16*) Hypothesis H16: (i3 + 1) < k1.  (*who*) 
        (*whoH17*) Hypothesis H17: k1 <= (len - 1).  (*who*) 
        (*whogoal2*) Lemma goal2:
                     (get (ofs2 + k1) (!! ar2 anon6)) =
                     (get (ofs1 + k1) (!! ar1 anon4)). (*who*) 
        Proof.
           assert (ofs2 + i3 <> ofs2 + k1) by omega.
           rewrite H15, get_set_neq, <- H14, <- H13; try omega; auto.
           apply H12; omega. Qed.
          
        
        
        (*whoendsec3*)
        End sec3. (*who*)
      
      (*whoendsec2*)
      End sec2. (*who*)
    
    (*whobeginsec4*)
    Section sec4. (*who*)
      (*whok2*) Variable k2: Z.  (*who*) 
      (*whoH18*) Hypothesis H18: (len - 1) < k2.  (*who*) 
      (*whoH19*) Hypothesis H19: k2 <= (len - 1).  (*who*) 
      (*whogoal3*) Lemma goal3:
                   (get (ofs2 + k2) (!! ar2 anon2)) =
                   (get (ofs1 + k2) (!! ar1 anon1)). (*who*) 
      Proof. apply False_rec; omega. Qed.
        
      
      
      (*whoendsec4*)
      End sec4. (*who*)
    
    (*whobeginsec5*)
    Section sec5. (*who*)
      (*whoi4*) Variable i4: Z.  (*who*) 
      (*whoH20*) Hypothesis H20: (len - 1) <= i4.  (*who*) 
      (*whoH21*) Hypothesis H21: i4 <= 0.  (*who*) 
      (*whom*) Variable m: kmap.  (*who*) 
      (*whoH22*) Hypothesis H22: (!! ar1 m) = (!! ar1 anon1).  (*who*) 
      (*whoH23*) Hypothesis H23:
                 (length (!! ar2 m)) = (length (!! ar2 anon2)).  (*who*) 
      (*whoH24*) Hypothesis H24:
                 forall (k3:Z),
                 (i4 < k3) ->
                 ((k3 <= (len - 1)) ->
                  ((get (ofs2 + k3) (!! ar2 m)) =
                   (get (ofs1 + k3) (!! ar1 m)))).  (*who*) 
      
      (*whobeginsec6*)
      Section sec6. (*who*)
        (*whok4*) Variable k4: Z.  (*who*) 
        (*whoH25*) Hypothesis H25: i4 < k4.  (*who*) 
        (*whoH26*) Hypothesis H26: k4 <= (len - 1).  (*who*) 
        (*whogoal4*) Lemma goal4:
                     (get (ofs2 + k4) (!! ar2 m)) =
                     (get (ofs1 + k4) (!! ar1 m)). (*who*) 
        (*whoendsec6*)
        End sec6. (*who*)
      
      (*whobeginsec7*)
      Section sec7. (*who*)
        (*whon*) Variable n: kmap.  (*who*) 
        (*whoH27*) Hypothesis H27: (!! ar1 n) = (!! ar1 anon1).  (*who*) 
        (*whoH28*) Hypothesis H28:
                   (length (!! ar2 n)) = (length (!! ar2 anon2)).  (*who*) 
        (*whoH29*) Hypothesis H29:
                   forall (k5:Z),
                   ((i4 + 1) < k5) ->
                   ((k5 <= (len - 1)) ->
                    ((get (ofs2 + k5) (!! ar2 n)) =
                     (get (ofs1 + k5) (!! ar1 n)))).  (*who*) 
        
        (*whobeginsec8*)
        Section sec8. (*who*)
          (*whok6*) Variable k6: Z.  (*who*) 
          (*whoH30*) Hypothesis H30: (i4 - 1) < k6.  (*who*) 
          (*whoH31*) Hypothesis H31: k6 <= (len - 1).  (*who*) 
          (*whogoal5*) Lemma goal5:
                       (get (ofs2 + k6) (!! ar2 n)) =
                       (get (ofs1 + k6) (!! ar1 n)). (*who*) 
          Proof. Admitted.
        
          
          
          (*whoendsec8*)
          End sec8. (*who*)
        
        (*whoendsec7*)
        End sec7. (*who*)
      
      (*whoendsec5*)
      End sec5. (*who*)
    
    (*whobeginsec9*)
    Section sec9. (*who*)
      (*whoanon7*) Variable anon7: kmap.  (*who*) 
      (*whoH32*) Hypothesis H32: (!! ar1 anon7) = (!! ar1 anon1).  (*who*) 
      (*whoH33*) Hypothesis H33:
                 (length (!! ar2 anon7)) = (length (!! ar2 anon2)).  (*who*) 
      (*whoH34*) Hypothesis H34:
                 forall (k7:Z),
                 ((min (len - 1) (0 - 1)) < k7) ->
                 ((k7 <= (len - 1)) ->
                  ((get (ofs2 + k7) (!! ar2 anon7)) =
                   (get (ofs1 + k7) (!! ar1 anon7)))).  (*who*) 
      (*whogoal6*) Lemma goal6: (!! ar1 anon) = (!! ar1 anon7). (*who*) 
      Proof. rewrite H32; auto. Qed.
        
      (*whogoal7*) Lemma goal7:
                                                                 (length
                                                                  (!! ar2
                                                                   anon7))
                                                                 =
                                                                 (length
                                                                  (!! ar2
                                                                   anon)). (*who*) 
      Proof. rewrite H33, H6; auto. Qed.
      
      
      
      (*whobeginsec10*)
      Section sec10. (*who*)
        (*whok8*) Variable k8: Z.  (*who*) 
        (*whoH35*) Hypothesis H35: 0 <= k8.  (*who*) 
        (*whoH36*) Hypothesis H36: k8 < len.  (*who*) 
        (*whogoal8*) Lemma goal8:
                     (get (ofs2 + k8) (!! ar2 anon7)) =
                     (get (ofs1 + k8) (!! ar1 anon7)). (*who*) 
        Proof.  apply H34; try omega. unfold min. Admitted.
          
        
        
        
        (*whoendsec10*)
        End sec10. (*who*)
      
      (*whoendsec9*)
      End sec9. (*who*)
    
    (*whoendsec1*)
    End sec1. (*who*)
  
  (*whobeginsec11*)
  Section sec11. (*who*)
    (*whoH37*) Hypothesis H37: ~ (ofs1 < ofs2).  (*who*) 
    
    (*whobeginsec12*)
    Section sec12. (*who*)
      (*whoanon8*) Variable anon8: kmap.  (*who*) 
      (*whoi5*) Variable i5: Z.  (*who*) 
      (*whoH38*) Hypothesis H38: 0 <= i5.  (*who*) 
      (*whoH39*) Hypothesis H39: i5 <= (len - 1).  (*who*) 
      (*whoH40*) Hypothesis H40: (!! ar1 anon8) = (!! ar1 anon1).  (*who*) 
      (*whoH41*) Hypothesis H41:
                 (length (!! ar2 anon8)) = (length (!! ar2 anon2)).  (*who*) 
      (*whoH42*) Hypothesis H42:
                 forall (k9:Z),
                 (0 <= k9) ->
                 ((k9 < i5) ->
                  ((get (ofs2 + k9) (!! ar2 anon8)) =
                   (get (ofs1 + k9) (!! ar1 anon8)))).  (*who*) 
      (*whoanon9*) Variable anon9: kmap.  (*who*) 
      (*whoH43*) Hypothesis H43: (!! ar1 anon8) = (!! ar1 anon9).  (*who*) 
      (*whoanon10*) Variable anon10: kmap.  (*who*) 
      (*whoH44*) Hypothesis H44: (!! ar2 anon8) = (!! ar2 anon10).  (*who*) 
      (*whoanon11*) Variable anon11: kmap.  (*who*) 
      (*whoH45*) Hypothesis H45:
                 (!! ar2 anon11) =
                 (set (ofs2 + i5) (get (ofs1 + i5) (!! ar1 anon9))
                  (!! ar2 anon10)).  (*who*) 
      (*whogoal9*) Lemma goal9: (!! ar1 anon9) = (!! ar1 anon1). (*who*) 
      Proof. transitivity (!! ar1 anon8); auto. Qed.
      (*whogoal10*) 
      Lemma goal10: (length (!! ar2 anon11)) = (length (!! ar2 anon2)). (*who*) 
      Proof. rewrite H45, <- H44, <- update_length; auto. Qed.
      
      
      
      (*whobeginsec13*)
      Section sec13. (*who*)
        (*whok10*) Variable k10: Z.  (*who*) 
        (*whoH46*) Hypothesis H46: 0 <= k10.  (*who*) 
        (*whoH47*) Hypothesis H47: k10 < (i5 + 1).  (*who*) 
        (*whogoal11*) Lemma goal11:
                      (get (ofs2 + k10) (!! ar2 anon11)) =
                      (get (ofs1 + k10) (!! ar1 anon9)). (*who*) 
        Proof.
          rewrite H45.
          case_eq (Z_eq_dec k10 i5); intros A B. 
          rewrite A, get_set_eq; try omega; auto.
          rewrite <- H44, H41, <- H6; omega.
          rewrite get_set_neq, <- H44, <- H43;try omega; auto. 
          apply H42; omega.
          rewrite <- H44, H41, <- H6; omega.
          rewrite <- H44, H41, <- H6; omega.
       Qed.
        
        
        
        (*whoendsec13*)
        End sec13. (*who*)
      
      (*whoendsec12*)
      End sec12. (*who*)
    
    (*whobeginsec14*)
    Section sec14. (*who*)
      (*whok11*) Variable k11: Z.  (*who*) 
      (*whoH48*) Hypothesis H48: 0 <= k11.  (*who*) 
      (*whoH49*) Hypothesis H49: k11 < 0.  (*who*) 
      (*whogoal12*) Lemma goal12:
                    (get (ofs2 + k11) (!! ar2 anon2)) =
                    (get (ofs1 + k11) (!! ar1 anon1)). (*who*) 
      Proof. apply False_rec; omega. Qed.
      
      
      
      (*whoendsec14*)
      End sec14. (*who*)
    
    (*whobeginsec15*)
    Section sec15. (*who*)
      (*whoi6*) Variable i6: Z.  (*who*) 
      (*whoH50*) Hypothesis H50: 0 <= i6.  (*who*) 
      (*whoH51*) Hypothesis H51: i6 <= (len - 1).  (*who*) 
      (*whom1*) Variable m1: kmap.  (*who*) 
      (*whoH52*) Hypothesis H52: (!! ar1 m1) = (!! ar1 anon1).  (*who*) 
      (*whoH53*) Hypothesis H53:
                 (length (!! ar2 m1)) = (length (!! ar2 anon2)).  (*who*) 
      (*whoH54*) Hypothesis H54:
                 forall (k12:Z),
                 (0 <= k12) ->
                 ((k12 < i6) ->
                  ((get (ofs2 + k12) (!! ar2 m1)) =
                   (get (ofs1 + k12) (!! ar1 m1)))).  (*who*) 
      
      (*whobeginsec16*)
      Section sec16. (*who*)
        (*whok13*) Variable k13: Z.  (*who*) 
        (*whoH55*) Hypothesis H55: 0 <= k13.  (*who*) 
        (*whoH56*) Hypothesis H56: k13 < i6.  (*who*) 
        (*whogoal13*) Lemma goal13:
                      (get (ofs2 + k13) (!! ar2 m1)) =
                      (get (ofs1 + k13) (!! ar1 m1)). (*who*) 
        Proof. apply H54; omega. Qed.
        
        
        (*whoendsec16*)
        End sec16. (*who*)
      
      (*whoendsec15*)
      End sec15. (*who*)
    
    (*whobeginsec17*)
    Section sec17. (*who*)
      (*whoanon12*) Variable anon12: kmap.  (*who*) 
      (*whoH57*) Hypothesis H57: (!! ar1 anon12) = (!! ar1 anon1).  (*who*) 
      (*whoH58*) Hypothesis H58:
                 (length (!! ar2 anon12)) = (length (!! ar2 anon2)).  (*who*) 
      (*whoH59*) Hypothesis H59:
                 forall (k14:Z),
                 (0 <= k14) ->
                 ((k14 < (max 0 ((len - 1) + 1))) ->
                  ((get (ofs2 + k14) (!! ar2 anon12)) =
                   (get (ofs1 + k14) (!! ar1 anon12)))).  (*who*) 
      (*whogoal14*) Lemma goal14: (!! ar1 anon) = (!! ar1 anon12). (*who*) 
      Proof. rewrite H57, H5; auto. Qed.
      (*whogoal15*) Lemma goal15:
                                                             (length
                                                              (!! ar2 anon12))
                                                             =
                                                             (length
                                                              (!! ar2 anon)). (*who*) 
      Proof.
          rewrite H58, H6; auto. Qed.
      
      
      
      (*whobeginsec18*)
      Section sec18. (*who*)
        (*whok15*) Variable k15: Z.  (*who*) 
        (*whoH60*) Hypothesis H60: 0 <= k15.  (*who*) 
        (*whoH61*) Hypothesis H61: k15 < len.  (*who*) 
        (*whogoal16*) Lemma goal16:
                      (get (ofs2 + k15) (!! ar2 anon12)) =
                      (get (ofs1 + k15) (!! ar1 anon12)). (*who*) 
        Proof. apply H59; auto. Admitted.
        
        
        
        (*whoendsec18*)
        End sec18. (*who*)
      
      (*whoendsec17*)
      End sec17. (*who*)
    
    (*whoendsec11*)
    End sec11. (*who*)
  
  (*whoendsec*)
  End sec. (*who*)
