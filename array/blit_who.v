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
  (*whoArra*) Require Import WhoArray. (*who*) (*whoa*) Variables a : Type.
  Variables r1 r2 : key.  (*who*) 
  (*whoar1*) Variable ar1: ref (array a) r1.  (*who*) 
  (*whoar2*) Variable ar2: ref (array a) r2.  (*who*) 
  (*whoofs1*) Variable ofs1: int.  (*who*) 
  (*whoofs2*) Variable ofs2: int.  (*who*) 
  (*whos*) Variable s: kmap.  (*who*) (*wholen*) Variable len: int.  (*who*) 
  (*whoH*) Hypothesis H: 0 <= len.  (*who*) 
  (*whoH1*) Hypothesis H1: 0 <= ofs1.  (*who*) 
  (*whoH2*) Hypothesis H2: 0 <= ofs2.  (*who*) 
  (*whoH3*) Hypothesis H3: ofs1 <= ((length (!! ar1 s)) - len).  (*who*) 
  (*whoH4*) Hypothesis H4: ofs2 <= ((length (!! ar2 s)) - len).  (*who*) 
  (*whos1*) Variable s1: kmap.  (*who*) 
  (*whoH5*) Hypothesis H5: (!! ar1 s) = (!! ar1 s1).  (*who*) 
  (*whos2*) Variable s2: kmap.  (*who*) 
  (*whoH6*) Hypothesis H6: (!! ar2 s) = (!! ar2 s2).  (*who*) 
  
  (*whobeginsec1*)
  Section sec1. (*who*)
    (*whoH7*) Hypothesis H7: ofs1 < ofs2.  (*who*) 
    
    (*whobeginsec2*)
    Section sec2. (*who*)
      (*whos3*) Variable s3: kmap.  (*who*) 
      (*whoi*) Variable i: int.  (*who*) 
      (*whoH8*) Hypothesis H8: (len - 1) <= i.  (*who*) 
      (*whoH9*) Hypothesis H9: i <= 0.  (*who*) 
      (*whoH10*) Hypothesis H10: (!! ar1 s3) = (!! ar1 s1).  (*who*) 
      (*whoH11*) Hypothesis H11:
                 (length (!! ar2 s3)) = (length (!! ar2 s2)).  (*who*) 
      (*whoH12*) Hypothesis H12:
                 forall (k9:int),
                 (i < k9) ->
                 ((k9 <= (len - 1)) ->
                  ((get (ofs2 + k9) (!! ar2 s3)) =
                   (get (ofs1 + k9) (!! ar1 s3)))).  (*who*) 
      (*whos4*) Variable s4: kmap.  (*who*) 
      (*whoH13*) Hypothesis H13: (!! ar1 s3) = (!! ar1 s4).  (*who*) 
      (*whos5*) Variable s5: kmap.  (*who*) 
      (*whoH14*) Hypothesis H14: (!! ar2 s3) = (!! ar2 s5).  (*who*) 
      (*whos6*) Variable s6: kmap.  (*who*) 
      (*whoH15*) Hypothesis H15:
                 (!! ar2 s6) =
                 (set (ofs2 + i) (get (ofs1 + i) (!! ar1 s4)) (!! ar2 s5)).  (*who*) 
      (*whogoal*) Lemma goal: (!! ar1 s4) = (!! ar1 s1). (*who*) 
      Proof. transitivity (!! ar1 s3); auto. Qed.
        
      (*whogoal1*) Lemma goal1: (length (!! ar2 s6)) = (length (!! ar2 s2)). (*who*) 
Proof. rewrite H15, <- update_length, <- H14; auto. Qed.
      (*whobeginsec3*)
      Section sec3. (*who*)
        (*whok*) Variable k: int.  (*who*) 
        (*whoH16*) Hypothesis H16: (i + 1) < k.  (*who*) 
        (*whoH17*) Hypothesis H17: k <= (len - 1).  (*who*) 
        (*whogoal2*) Lemma goal2:
                     (get (ofs2 + k) (!! ar2 s6)) =
                     (get (ofs1 + k) (!! ar1 s4)). (*who*) 
        Proof.
          assert (ofs2 + i <> ofs2 + k) by omega.
          rewrite H15, get_set_neq, <- H14, <- H13; try omega; auto.
          apply H12; omega. 
        Qed. 
        (*whoendsec3*)
        End sec3. (*who*)
      
      (*whoendsec2*)
      End sec2. (*who*)
    
    (*whobeginsec4*)
    Section sec4. (*who*)
      (*whok1*) Variable k1: int.  (*who*) 
      (*whoH18*) Hypothesis H18: (len - 1) < k1.  (*who*) 
      (*whoH19*) Hypothesis H19: k1 <= (len - 1).  (*who*) 
      (*whogoal3*) Lemma goal3:
                   (get (ofs2 + k1) (!! ar2 s2)) =
                   (get (ofs1 + k1) (!! ar1 s1)). (*who*) 
      Proof. apply False_rec; omega. Qed.
      
      (*whoendsec4*)
      End sec4. (*who*)
    
    (*whobeginsec5*)
    Section sec5. (*who*)
      (*whoi1*) Variable i1: int.  (*who*) 
      (*whoH20*) Hypothesis H20: (len - 1) <= i1.  (*who*) 
      (*whoH21*) Hypothesis H21: i1 <= 0.  (*who*) 
      (*whom*) Variable m: kmap.  (*who*) 
      (*whoH22*) Hypothesis H22: (!! ar1 m) = (!! ar1 s1).  (*who*) 
      (*whoH23*) Hypothesis H23: (length (!! ar2 m)) = (length (!! ar2 s2)).  (*who*) 
      
      (*whoH24*) Hypothesis H24:
                 forall (k10:int),
                 (i1 < k10) ->
                 ((k10 <= (len - 1)) ->
                  ((get (ofs2 + k10) (!! ar2 m)) =
                   (get (ofs1 + k10) (!! ar1 m)))).  (*who*) 
      
      (*whobeginsec6*)
      Section sec6. (*who*)
        (*whok2*) Variable k2: int.  (*who*) 
        (*whoH25*) Hypothesis H25: i1 < k2.  (*who*) 
        (*whoH26*) Hypothesis H26: k2 <= (len - 1).  (*who*) 
        (*whogoal4*) Lemma goal4:
                     (get (ofs2 + k2) (!! ar2 m)) =
                     (get (ofs1 + k2) (!! ar1 m)). (*who*) 
        Proof. apply H24; omega. Qed.
        (*whoendsec6*)
        End sec6. (*who*)
      
      (*whobeginsec7*)
      Section sec7. (*who*)
        (*whon*) Variable n: kmap.  (*who*) 
        (*whoH27*) Hypothesis H27: (!! ar1 n) = (!! ar1 s1).  (*who*) 
        (*whoH28*) Hypothesis H28:
                   (length (!! ar2 n)) = (length (!! ar2 s2)).  (*who*) 
        (*whoH29*) Hypothesis H29:
                   forall (k11:int),
                   ((i1 + 1) < k11) ->
                   ((k11 <= (len - 1)) ->
                    ((get (ofs2 + k11) (!! ar2 n)) =
                     (get (ofs1 + k11) (!! ar1 n)))).  (*who*) 
        
        (*whobeginsec8*)
        Section sec8. (*who*)
          (*whok3*) Variable k3: int.  (*who*) 
          (*whoH30*) Hypothesis H30: (i1 - 1) < k3.  (*who*) 
          (*whoH31*) Hypothesis H31: k3 <= (len - 1).  (*who*) 
          (*whogoal5*) Lemma goal5:
                       (get (ofs2 + k3) (!! ar2 n)) =
                       (get (ofs1 + k3) (!! ar1 n)). (*who*) 
          Proof. Admitted.
          (*whoendsec8*)
          End sec8. (*who*)
        
        (*whoendsec7*)
        End sec7. (*who*)
      
      (*whoendsec5*)
      End sec5. (*who*)
    
    (*whobeginsec9*)
    Section sec9. (*who*)
      (*whos7*) Variable s7: kmap.  (*who*) 
      (*whoH32*) Hypothesis H32: (!! ar1 s7) = (!! ar1 s1).  (*who*) 
      (*whoH33*) Hypothesis H33:
                 (length (!! ar2 s7)) = (length (!! ar2 s2)).  (*who*) 
      (*whoH34*) Hypothesis H34:
                 forall (k12:int),
                 ((min (len - 1) (0 - 1)) < k12) ->
                 ((k12 <= (len - 1)) ->
                  ((get (ofs2 + k12) (!! ar2 s7)) =
                   (get (ofs1 + k12) (!! ar1 s7)))).  (*who*) 
      (*whogoal6*) Lemma goal6: (!! ar1 s) = (!! ar1 s7). (*who*) 
      Proof. rewrite H32; auto. Qed.
      (*whogoal7*) Lemma goal7: (length (!! ar2 s7)) = (length (!! ar2 s)). (*who*) 
      Proof. rewrite H33, H6; auto. Qed.
      
      (*whobeginsec10*)
      Section sec10. (*who*)
        (*whok4*) Variable k4: int.  (*who*) 
        (*whoH35*) Hypothesis H35: 0 <= k4.  (*who*) 
        (*whoH36*) Hypothesis H36: k4 < len.  (*who*) 
        (*whogoal8*) Lemma goal8:
                     (get (ofs2 + k4) (!! ar2 s7)) =
                     (get (ofs1 + k4) (!! ar1 s7)). (*who*) 
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
      (*whos8*) Variable s8: kmap.  (*who*) 
      (*whoi2*) Variable i2: int.  (*who*) 
      (*whoH38*) Hypothesis H38: 0 <= i2.  (*who*) 
      (*whoH39*) Hypothesis H39: i2 <= (len - 1).  (*who*) 
      (*whoH40*) Hypothesis H40: (!! ar1 s8) = (!! ar1 s1).  (*who*) 
      (*whoH41*) Hypothesis H41:
                 (length (!! ar2 s8)) = (length (!! ar2 s2)).  (*who*) 
      (*whoH42*) Hypothesis H42:
                 forall (k13:int),
                 (0 <= k13) ->
                 ((k13 < i2) ->
                  ((get (ofs2 + k13) (!! ar2 s8)) =
                   (get (ofs1 + k13) (!! ar1 s8)))).  (*who*) 
      (*whos9*) Variable s9: kmap.  (*who*) 
      (*whoH43*) Hypothesis H43: (!! ar1 s8) = (!! ar1 s9).  (*who*) 
      (*whos10*) Variable s10: kmap.  (*who*) 
      (*whoH44*) Hypothesis H44: (!! ar2 s8) = (!! ar2 s10).  (*who*) 
      (*whos11*) Variable s11: kmap.  (*who*) 
      (*whoH45*) Hypothesis H45:
                 (!! ar2 s11) =
                 (set (ofs2 + i2) (get (ofs1 + i2) (!! ar1 s9)) (!! ar2 s10)).  (*who*) 
      (*whogoal9*) Lemma goal9: (!! ar1 s9) = (!! ar1 s1). (*who*) 
        Proof. transitivity (!! ar1 s8); auto. Qed.
      (*whogoal10*) Lemma goal10:
                    (length (!! ar2 s11)) = (length (!! ar2 s2)). (*who*) 
      Proof. rewrite H45, <- H44, <- update_length; auto. Qed.
      
      (*whobeginsec13*)
      Section sec13. (*who*)
        (*whok5*) Variable k5: int.  (*who*) 
        (*whoH46*) Hypothesis H46: 0 <= k5.  (*who*) 
        (*whoH47*) Hypothesis H47: k5 < (i2 + 1).  (*who*) 
        (*whogoal11*) Lemma goal11:
                      (get (ofs2 + k5) (!! ar2 s11)) =
                      (get (ofs1 + k5) (!! ar1 s9)). (*who*) 
        Proof.
          rewrite H45.
          case_eq (Z_eq_dec k5 i2); intros A B. 
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
      (*whok6*) Variable k6: int.  (*who*) 
      (*whoH48*) Hypothesis H48: 0 <= k6.  (*who*) 
      (*whoH49*) Hypothesis H49: k6 < 0.  (*who*) 
      (*whogoal12*) Lemma goal12:
                    (get (ofs2 + k6) (!! ar2 s2)) =
                    (get (ofs1 + k6) (!! ar1 s1)). (*who*) 
      Proof. apply False_rec; omega. Qed.
      (*whoendsec14*)
      End sec14. (*who*)
    
    (*whobeginsec15*)
    Section sec15. (*who*)
      (*whoi3*) Variable i3: int.  (*who*) 
      (*whoH50*) Hypothesis H50: 0 <= i3.  (*who*) 
      (*whoH51*) Hypothesis H51: i3 <= (len - 1).  (*who*) 
      (*whom1*) Variable m1: kmap.  (*who*) 
      (*whoH52*) Hypothesis H52: (!! ar1 m1) = (!! ar1 s1).  (*who*) 
      (*whoH53*) Hypothesis H53:
                 (length (!! ar2 m1)) = (length (!! ar2 s2)).  (*who*) 
      (*whoH54*) Hypothesis H54:
                 forall (k14:int),
                 (0 <= k14) ->
                 ((k14 < i3) ->
                  ((get (ofs2 + k14) (!! ar2 m1)) =
                   (get (ofs1 + k14) (!! ar1 m1)))).  (*who*) 
      
      (*whobeginsec16*)
      Section sec16. (*who*)
        (*whok7*) Variable k7: int.  (*who*) 
        (*whoH55*) Hypothesis H55: 0 <= k7.  (*who*) 
        (*whoH56*) Hypothesis H56: k7 < i3.  (*who*) 
        (*whogoal13*) Lemma goal13:
                      (get (ofs2 + k7) (!! ar2 m1)) =
                      (get (ofs1 + k7) (!! ar1 m1)). (*who*) 
        Proof. apply H54; omega. Qed.

        (*whoendsec16*)
        End sec16. (*who*)
      
      (*whoendsec15*)
      End sec15. (*who*)
    
    (*whobeginsec17*)
    Section sec17. (*who*)
      (*whos12*) Variable s12: kmap.  (*who*) 
      (*whoH57*) Hypothesis H57: (!! ar1 s12) = (!! ar1 s1).  (*who*) 
      (*whoH58*) Hypothesis H58:
                 (length (!! ar2 s12)) = (length (!! ar2 s2)).  (*who*) 
      (*whoH59*) Hypothesis H59:
                 forall (k15:int),
                 (0 <= k15) ->
                 ((k15 < (max 0 ((len - 1) + 1))) ->
                  ((get (ofs2 + k15) (!! ar2 s12)) =
                   (get (ofs1 + k15) (!! ar1 s12)))).  (*who*) 
      (*whogoal14*) Lemma goal14: (!! ar1 s) = (!! ar1 s12). (*who*) 
      Proof. rewrite H57, H5; auto. Qed.


      (*whogoal15*) Lemma goal15:
                    (length (!! ar2 s12)) = (length (!! ar2 s)). (*who*) 
      Proof. rewrite H58, H6; auto. Qed.
      
      (*whobeginsec18*)
      Section sec18. (*who*)
        (*whok8*) Variable k8: int.  (*who*) 
        (*whoH60*) Hypothesis H60: 0 <= k8.  (*who*) 
        (*whoH61*) Hypothesis H61: k8 < len.  (*who*) 
        (*whogoal16*) Lemma goal16:
                      (get (ofs2 + k8) (!! ar2 s12)) =
                      (get (ofs1 + k8) (!! ar1 s12)). (*who*) 
        Proof. apply H59; auto. Admitted.
        (*whoendsec18*)
        End sec18. (*who*)
      
      (*whoendsec17*)
      End sec17. (*who*)
    
    (*whoendsec11*)
    End sec11. (*who*)
  
  (*whoendsec*)
  End sec. (*who*)
