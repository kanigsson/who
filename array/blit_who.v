Set Implicit Arguments.
Section sec.
  Require Import WhoArith.
  Require Import WhoMap.
  Require Import WhoArray.
  Require Import WhoList.
  Variables a : Type.
  
  Variable r2:  key. 
  Variable r1:  key. 
  Variable ofs1:  int. 
  Variable ofs2:  int. 
  Variable r11:  array a. 
  Variable r21:  array a. 
  Variable l:  int. 
  Hypothesis H:  0 <= l. 
  Hypothesis H1:  0 <= ofs1. 
  Hypothesis H2:  0 <= ofs2. 
  Hypothesis H3:  ofs1 <= ((len r11) - l). 
  Hypothesis H4:  ofs2 <= ((len r21) - l). 
  Section sec1.
    Hypothesis H5:  ofs1 < ofs2. 
    Section sec2.
      Variable r12:  array a. 
      Variable r22:  array a. 
      Variable i:  int. 
      Hypothesis H6:  r12 = r11. 
      Hypothesis H7:  (len r22) = (len r21). 
      Hypothesis H8:  0 <= i. 
      Hypothesis H9:  i <= (l - 1). 
      Hypothesis H10:
         forall (k:int),
         (i < k) ->
         ((k <= (l - 1)) -> ((get (ofs2 + k) r22) = (get (ofs1 + k) r12))). 
      Lemma goal:
        (len (set (ofs2 + i) (get (ofs1 + i) r12) r22)) = (len r21).
        Proof.
        rewrite <- update_len; auto. Qed.
        
      Section sec3.
        Variable k1:  int. 
        Hypothesis H11:  (i - 1) < k1. 
        Hypothesis H12:  k1 <= (l - 1). 
        Lemma goal1:
          (get (ofs2 + k1) (set (ofs2 + i) (get (ofs1 + i) r12) r22)) =
          (get (ofs1 + k1) r12).
          Proof.     
            case_eq (Z_eq_dec i k1); intros A B. 
            rewrite A, get_set_eq; auto; try omega.
            rewrite get_set_neq; try omega. apply H10; omega.
          Qed.

        End sec3.
      End sec2.
    Lemma goal2: r11 = r11.
      Proof. auto. Qed.
      
    Lemma goal3: (len r21) = (len r21).
      Proof. auto. Qed.
      
    Section sec4.
      Variable k2:  int. 
      Hypothesis H13:  (l - 1) < k2. 
      Hypothesis H14:  k2 <= (l - 1). 
      Lemma goal4:
        (get (ofs2 + k2) r21) = (get (ofs1 + k2) r11).
        Proof.
      apply False_rec; omega.
      Qed.
        
      End sec4.
    Section sec5.
      Variable i1:  int. 
      Hypothesis H15:  0 <= i1. 
      Hypothesis H16:  i1 <= (l - 1). 
      Variable r13:  array a. 
      Variable r23:  array a. 
      Hypothesis H17:  r13 = r11. 
      Hypothesis H18:  (len r23) = (len r21). 
      Hypothesis H19:
         forall (k3:int),
         (i1 < k3) ->
         ((k3 <= (l - 1)) -> ((get (ofs2 + k3) r23) = (get (ofs1 + k3) r13))). 
      Section sec6.
        Variable k4:  int. 
        Hypothesis H20:  i1 < k4. 
        Hypothesis H21:  k4 <= (l - 1). 
        Lemma goal5:
          (get (ofs2 + k4) r23) = (get (ofs1 + k4) r13).
          Proof.
          auto. Qed.
          
        End sec6.
      End sec5.
    Section sec7.
      Variable r14:  array a. 
      Variable r24:  array a. 
      Hypothesis H22:  r14 = r11. 
      Hypothesis H23:  (len r24) = (len r21). 
      Hypothesis H24:
         forall (k5:int),
         ((min (l - 1) (0 - 1)) < k5) ->
         ((k5 <= (l - 1)) -> ((get (ofs2 + k5) r24) = (get (ofs1 + k5) r14))). 
      Lemma goal6: r11 = r14.
        Proof. auto. Qed.
        
      Section sec8.
        Variable k6:  int. 
        Hypothesis H25:  0 <= k6. 
        Hypothesis H26:  k6 < l. 
        Lemma goal7:
          (get (ofs2 + k6) r24) = (get (ofs1 + k6) r14).
          Proof.
            apply H24; try omega; admit. Qed.
        End sec8.
      End sec7.
    End sec1.
  Section sec9.
    Hypothesis H27:  ~ (ofs1 < ofs2). 
    Section sec10.
      Variable r15:  array a. 
      Variable r25:  array a. 
      Variable i2:  int. 
      Hypothesis H28:  r15 = r11. 
      Hypothesis H29:  (len r25) = (len r21). 
      Hypothesis H30:  0 <= i2. 
      Hypothesis H31:  i2 <= (l - 1). 
      Hypothesis H32:
         forall (k7:int),
         (0 <= k7) ->
         ((k7 < i2) -> ((get (ofs2 + k7) r25) = (get (ofs1 + k7) r15))). 
      Lemma goal8:
        (len (set (ofs2 + i2) (get (ofs1 + i2) r15) r25)) = (len r21).
        Proof.
        rewrite <- update_len; auto. Qed.
        
      Section sec11.
        Variable k8:  int. 
        Hypothesis H33:  0 <= k8. 
        Hypothesis H34:  k8 < (i2 + 1). 
        Lemma goal9:
          (get (ofs2 + k8) (set (ofs2 + i2) (get (ofs1 + i2) r15) r25)) =
          (get (ofs1 + k8) r15).
          Proof.
            case_eq (Z_eq_dec k8 i2); intros A B.
            rewrite A, get_set_eq; try omega; auto.
            rewrite get_set_neq; try omega; auto. apply H32; try omega.
          Qed.
          
        End sec11.
      End sec10.
    Lemma goal10: r11 = r11.
      Proof.
        auto.
      Qed.
      
    Lemma goal11: (len r21) = (len r21).
      Proof.
        auto. Qed.
      
    Section sec12.
      Variable k9:  int. 
      Hypothesis H35:  0 <= k9. 
      Hypothesis H36:  k9 < 0. 
      Lemma goal12:
        (get (ofs2 + k9) r21) = (get (ofs1 + k9) r11).
        Proof.
          apply False_rec; omega. Qed.
        
      End sec12.
    Section sec13.
      Variable i3:  int. 
      Hypothesis H37:  0 <= i3. 
      Hypothesis H38:  i3 <= (l - 1). 
      Variable r16:  array a. 
      Variable r26:  array a. 
      Hypothesis H39:  r16 = r11. 
      Hypothesis H40:  (len r26) = (len r21). 
      Hypothesis H41:
         forall (k10:int),
         (0 <= k10) ->
         ((k10 < i3) -> ((get (ofs2 + k10) r26) = (get (ofs1 + k10) r16))). 
      Section sec14.
        Variable k11:  int. 
        Hypothesis H42:  0 <= k11. 
        Hypothesis H43:  k11 < i3. 
        Lemma goal13:
          (get (ofs2 + k11) r26) = (get (ofs1 + k11) r16).
          Proof.
            auto. Qed.
          
        End sec14.
      End sec13.
    Section sec15.
      Variable r17:  array a. 
      Variable r27:  array a. 
      Hypothesis H44:  r17 = r11. 
      Hypothesis H45:  (len r27) = (len r21). 
      Hypothesis H46:
         forall (k12:int),
         (0 <= k12) ->
         ((k12 < (max 0 ((l - 1) + 1))) ->
          ((get (ofs2 + k12) r27) = (get (ofs1 + k12) r17))). 
      Lemma goal14: r11 = r17.
        Proof.
          auto. Qed.
        
      Section sec16.
        Variable k13:  int. 
        Hypothesis H47:  0 <= k13. 
        Hypothesis H48:  k13 < l. 
        Lemma goal15:
          (get (ofs2 + k13) r27) = (get (ofs1 + k13) r17).
          Proof.
            apply H46; auto. rewrite Zmax_right; omega. Qed.
          
        End sec16.
      End sec15.
    End sec9.
  End sec.
