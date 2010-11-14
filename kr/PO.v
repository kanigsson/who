Require Export KR.

(*who*) Section sec_12.
Parameter f0 : forest.
Parameter k : ((unit -> (state -> Prop)) *
               (unit -> (state -> (state -> (unit -> Prop))))).
Parameter bits : state.
Parameter f : forest.
Hypothesis Hypo :
(forall (bits_1 : state) (bits_2 : state) ,
 (((((snd(k )  tt)  bits_1 )  bits_2 )  tt) ->
  ((((mirrorf   bits_1 )  bits_2 )  f0 ) /\
   (((eq_out   bits_1 )  bits_2 )  f0 )))).
Hypothesis Hypo_1 :
(forall (bits_3 : state) ,
 ((validf   f0 ) -> (((anyf   bits_3 )  f0 ) -> ((fst(k )  tt)  bits_3 )))).
Hypothesis Hypo_2 :
((anyf   bits )  ((append   f )  f0 )).
Hypothesis Hypo_3 :
(validf   ((append   f )  f0 )).
 (*whoEND*)

(*who*) Section sec_1.
Hypothesis Hypo_4 : ((is_nil   f ) = true).
 (*whoEND*)

(*who*) Lemma PO :
((fst(k )  tt)  bits ). (*whoEND*)
Proof.
  destruct f; simpl in *|-*.
  intuition.
  discriminate Hypo_4.
Qed.

(*who*) Section sec.
Parameter bits_4 : state.
Parameter anon : unit.
Hypothesis Hypo_5 :
((((snd(k )  tt)  bits )  bits_4 )  tt).
 (*whoEND*)

(*who*) Lemma PO_1 :
(((mirrorf   bits )  bits_4 )  ((append   f )  f0 )). (*whoEND*)
Proof.
  destruct f; simpl in *|-*; [clear Hypo_4 | discriminate].
  elim (Hypo bits bits_4); intuition.
Qed.

(*who*) Lemma PO_2 :
(((eq_out   bits )  bits_4 )  ((append   f )  f0 )). (*whoEND*)
Proof.
  destruct f; simpl in *|-*; [clear Hypo_4 | discriminate].
  elim (Hypo bits bits_4); intuition.
Qed.

(*who*) End sec. (*whoEND*)

(*who*) End sec_1. (*whoEND*)

(*who*) Section sec_11.
Hypothesis Hypo_6 :
((is_nil   f ) = false).
 (*whoEND*)

(*who*) Section sec_4.
Hypothesis Hypo_7 :
((is_white   ((get   bits )  (nodi   (head   f )))) = true).
 (*whoEND*)

(*who*) Lemma PO_3 :
(validf   ((append   (tail   f ))  f0 )). (*whoEND*)
Proof.
  destruct f; simpl in *|-*; [discriminate | idtac].
  eauto.
Qed.

(*who*) Lemma PO_4 :
((anyf   bits )  ((append   (tail   f ))  f0 )). (*whoEND*)
Proof.
  destruct f; simpl in *|-*; [discriminate | clear Hypo_6].
  eauto.
Qed.

(*who*) Section sec_3.
Parameter bits_5 : state.
Parameter anon_1 : unit.
Hypothesis Hypo_8 :
(((eq_out   bits )  bits_5 )  ((append   (tail   f ))  f0 )).
Hypothesis Hypo_9 :
(((mirrorf   bits )  bits_5 )  ((append   (tail   f ))  f0 )).
 (*whoEND*)

(*who*) Lemma PO_5 :
(validf   ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))). (*whoEND*)
Proof.
  destruct f; simpl in *|-*; [discriminate | clear Hypo_6].
  destruct t; simpl in *|-*.
  eauto.
Qed.

(*who*) Lemma PO_6 :
((anyf   (((set   bits_5 )  (nodi   (head   f )))  Black )) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))). (*whoEND*)
Proof.
  destruct f; simpl in *|-*; [discriminate | clear Hypo_6].
  destruct t; simpl in *|-*.
  apply frame_anyf with bits_5.
  apply any_append.
  apply frame_anyf with bits.
  inversion Hypo_2.
  inversion H1; auto.
  inversion H3; auto.
  eauto.
  eauto.
  red; intros; assert (i <> n).
  assert (~(inf n (append f2 (append f1 f0)))). eauto.
  intro; subst; eauto.  
  unfold set; case (eq_nat_dec n i); auto.
  intro; absurd (i=n); auto.
Qed.


(*who*) Section sec_2.
Parameter bits_6 : state.
Parameter anon_2 : unit.
Hypothesis Hypo_10 :
(((eq_out   (((set   bits_5 )  (nodi   (head   f )))  Black ))  bits_6 ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))).
Hypothesis Hypo_11 :
(((mirrorf   (((set   bits_5 )  (nodi   (head   f )))  Black ))  bits_6 ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))).
 (*whoEND*)

(*who*) Lemma PO_7 :
(((mirrorf   bits )  bits_6 )  ((append   f )  f0 )). (*whoEND*)
Proof.
  destruct f; simpl in *|-*; [discriminate | clear Hypo_6].
  destruct t; simpl in *|-*.
Admitted.

(*who*) Lemma PO_8 :
(((eq_out   bits )  bits_6 )  ((append   f )  f0 )). (*whoEND*)
Proof.
   destruct f; simpl in *|-*; [discriminate | clear Hypo_6].
   destruct t; simpl in *|-*.
  apply eq_out_trans with (set bits_5 n Black).
  apply eq_out_trans with bits_5.
  intros i hi.
  unfold eq_out in Hypo_8; apply Hypo_8.
  intro; elim hi; auto.
  intros i hi.
  unfold set; case (eq_nat_dec n i); intro.
  subst; elim hi; auto.
  reflexivity.
  intros i hi.
  unfold eq_out in Hypo_10; apply Hypo_10.
  intro; elim hi.
  elim (inf_append_inv _ _ _ H); eauto.
Qed.

(*who*) End sec_2. (*whoEND*)

(*who*) End sec_3. (*whoEND*)

(*who*) End sec_4. (*whoEND*)

(*who*) Section sec_7.
Hypothesis Hypo_12 :
((is_white   ((get   bits )  (nodi   (head   f )))) = false).
 (*whoEND*)

(*who*) Lemma PO_9 :
(validf   ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))). (*whoEND*)
Admitted.

(*who*) Lemma PO_10 :
((anyf   bits ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))). (*whoEND*)
Admitted.

(*who*) Section sec_6.
Parameter bits_7 : state.
Parameter anon_3 : unit.
Hypothesis Hypo_13 :
(((eq_out   bits )  bits_7 ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))).
Hypothesis Hypo_14 :
(((mirrorf   bits )  bits_7 ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))).
 (*whoEND*)

(*who*) Lemma PO_11 :
(validf   ((append   (tail   f ))  f0 )). (*whoEND*)
Admitted.

(*who*) Lemma PO_12 :
((anyf   (((set   bits_7 )  (nodi   (head   f )))  White )) 
 ((append   (tail   f ))  f0 )). (*whoEND*)
Admitted.

(*who*) Section sec_5.
Parameter bits_8 : state.
Parameter anon_4 : unit.
Hypothesis Hypo_15 :
(((eq_out   (((set   bits_7 )  (nodi   (head   f )))  White ))  bits_8 ) 
 ((append   (tail   f ))  f0 )).
Hypothesis Hypo_16 :
(((mirrorf   (((set   bits_7 )  (nodi   (head   f )))  White ))  bits_8 ) 
 ((append   (tail   f ))  f0 )).
 (*whoEND*)

(*who*) Lemma PO_13 :
(((mirrorf   bits )  bits_8 )  ((append   f )  f0 )). (*whoEND*)
Admitted.

(*who*) Lemma PO_14 :
(((eq_out   bits )  bits_8 )  ((append   f )  f0 )). (*whoEND*)
Admitted.

(*who*) End sec_5. (*whoEND*)

(*who*) End sec_6. (*whoEND*)

(*who*) End sec_7. (*whoEND*)

(*who*) Section sec_10.
Parameter bits_9 : state.
Parameter anon_5 : unit.
Hypothesis Hypo_17 :
((anyf   bits_9 )  ((append   (tail   f ))  f0 )).
Hypothesis Hypo_18 :
(validf   ((append   (tail   f ))  f0 )).
 (*whoEND*)

(*who*) Section sec_8.
Parameter bits_10 : state.
Hypothesis Hypo_19 : (validf   f0 ).
Hypothesis Hypo_20 :
((anyf   bits_10 )  f0 ).
 (*whoEND*)

(*who*) Lemma PO_15 :
((fst(k )  tt)  bits_10 ). (*whoEND*)
Proof.
  intuition.
Qed.

(*who*) End sec_8. (*whoEND*)

(*who*) Section sec_9.
Parameter bits_11 : state.
Parameter bits_12 : state.
Hypothesis Hypo_21 :
((((snd(k )  tt)  bits_11 )  bits_12 )  tt).
 (*whoEND*)

(*who*) Lemma PO_16 :
(((mirrorf   bits_11 )  bits_12 )  f0 ). (*whoEND*)
Proof.
  intros.
  destruct (Hypo bits_11 bits_12); auto.
Qed.

(*who*) Lemma PO_17 :
(((eq_out   bits_11 )  bits_12 )  f0 ). (*whoEND*)
Proof.
  intros.
  destruct (Hypo bits_11 bits_12); auto.
Qed.

(*who*) End sec_9. (*whoEND*)

(*who*) End sec_10. (*whoEND*)

(*who*) End sec_11. (*whoEND*)

(*who*) End sec_12. (*whoEND*)



