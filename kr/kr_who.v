(*who*) Require Import ZArith. (*whoEND*)

(*who*) Open Scope Z_scope. (*whoEND*)

(*who*) Definition tree :
Set. (*whoEND*)

Admitted.
(*who*) Definition forest :
Set. (*whoEND*)

Admitted.
(*who*) Definition node  :
(Z -> (forest -> tree)). (*whoEND*)

Admitted.
(*who*) Definition nodi  :
(tree -> Z). (*whoEND*)

Admitted.
(*who*) Definition nodf  :
(tree -> forest). (*whoEND*)

Admitted.
(*who*) Definition nil  :
forest. (*whoEND*)

Admitted.
(*who*) Definition cons  :
(tree -> (forest -> forest)). (*whoEND*)

Admitted.
(*who*) Definition append  :
(forest -> (forest -> forest)). (*whoEND*)

Admitted.
(*who*) Definition is_nil  :
(forest -> bool). (*whoEND*)

Admitted.
(*who*) Definition head  :
(forest -> tree). (*whoEND*)

Admitted.
(*who*) Definition tail  :
(forest -> forest). (*whoEND*)

Admitted.
(*who*) Definition color :
Set. (*whoEND*)

Admitted.
(*who*) Definition black  :
color. (*whoEND*)

Admitted.
(*who*) Definition white  :
color. (*whoEND*)

Admitted.
(*who*) Definition is_white  :
(color -> bool). (*whoEND*)

Admitted.
(*who*) Definition state :
Set. (*whoEND*)

Admitted.
(*who*) Definition get  :
(state -> (Z -> color)). (*whoEND*)

Admitted.
(*who*) Definition set  :
(state -> (Z -> (color -> state))). (*whoEND*)

Admitted.
(*who*) Definition anyf  :
(state -> (forest -> Prop)). (*whoEND*)

Admitted.
(*who*) Definition mirrorf  :
(state -> (state -> (forest -> Prop))). (*whoEND*)

Admitted.
(*who*) Definition evenf  :
(forest -> Prop). (*whoEND*)

Admitted.
(*who*) Definition oddf  :
(forest -> Prop). (*whoEND*)

Admitted.
(*who*) Definition validf  :
(forest -> Prop). (*whoEND*)

Admitted.
(*who*) Definition eq_out  :
(state -> (state -> (forest -> Prop))). (*whoEND*)

Admitted.
(*who*) Section sec_12.
Parameter e : Set.
Parameter f0 : forest.
Parameter k : ((unit -> (state -> (e -> Prop))) *
               (unit -> (state -> (e -> (state -> (e -> (unit -> Prop))))))).
Parameter bits : state.
Parameter e_1 : e.
Parameter f : forest.
Hypothesis Hypo :
(forall (bits_1 : state) (e_2 : e) (bits_2 : state) (e_3 : e) ,
 (((((((snd(k )  tt)  bits_1 )  e_2 )  bits_2 )  e_3 )  tt) ->
  ((((mirrorf   bits_1 )  bits_2 )  f0 ) /\
   (((eq_out   bits_1 )  bits_2 )  f0 )))).
Hypothesis Hypo_1 :
(forall (bits_3 : state) (e_4 : e) ,
 ((validf   f0 ) ->
  (((anyf   bits_3 )  f0 ) -> (((fst(k )  tt)  bits_3 )  e_4 )))).
Hypothesis Hypo_2 :
((anyf   bits )  ((append   f )  f0 )).
Hypothesis Hypo_3 :
(validf   ((append   f )  f0 )).
 (*whoEND*)

Admitted.
(*who*) Section sec_1.
Hypothesis Hypo_4 : ((is_nil   f ) = true).
 (*whoEND*)

(*who*) Lemma PO :
(((fst(k )  tt)  bits )  e_1 ). (*whoEND*)

(*who*) Section sec.
Parameter bits_4 : state.
Parameter e_5 : e.
Parameter anon : unit.
Hypothesis Hypo_5 :
((((((snd(k )  tt)  bits )  e_1 )  bits_4 )  e_5 )  tt).
 (*whoEND*)

Admitted.
(*who*) Lemma PO_1 :
(((mirrorf   bits )  bits_4 )  ((append   f )  f0 )). (*whoEND*)

(*who*) Lemma PO_2 :
(((eq_out   bits )  bits_4 )  ((append   f )  f0 )). (*whoEND*)

Admitted.
(*who*) End sec. (*whoEND*)

Admitted.
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

(*who*) Lemma PO_4 :
((anyf   bits )  ((append   (tail   f ))  f0 )). (*whoEND*)

Admitted.
(*who*) Section sec_3.
Parameter bits_5 : state.
Parameter e_6 : e.
Parameter anon_1 : unit.
Hypothesis Hypo_8 :
(((eq_out   bits )  bits_5 )  ((append   (tail   f ))  f0 )).
Hypothesis Hypo_9 :
(((mirrorf   bits )  bits_5 )  ((append   (tail   f ))  f0 )).
 (*whoEND*)

Admitted.
(*who*) Lemma PO_5 :
(validf   ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))). (*whoEND*)

(*who*) Lemma PO_6 :
((anyf   (((set   bits_5 )  (nodi   (head   f )))  black )) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))). (*whoEND*)

Admitted.
(*who*) Section sec_2.
Parameter bits_6 : state.
Parameter e_7 : e.
Parameter anon_2 : unit.
Hypothesis Hypo_10 :
(((eq_out   (((set   bits_5 )  (nodi   (head   f )))  black ))  bits_6 ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))).
Hypothesis Hypo_11 :
(((mirrorf   (((set   bits_5 )  (nodi   (head   f )))  black ))  bits_6 ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))).
 (*whoEND*)

Admitted.
(*who*) Lemma PO_7 :
(((mirrorf   bits )  bits_6 )  ((append   f )  f0 )). (*whoEND*)

(*who*) Lemma PO_8 :
(((eq_out   bits )  bits_6 )  ((append   f )  f0 )). (*whoEND*)

Admitted.
(*who*) End sec_2. (*whoEND*)

Admitted.
(*who*) End sec_3. (*whoEND*)

(*who*) End sec_4. (*whoEND*)

(*who*) Section sec_7.
Hypothesis Hypo_12 :
((is_white   ((get   bits )  (nodi   (head   f )))) = false).
 (*whoEND*)

(*who*) Lemma PO_9 :
(validf   ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))). (*whoEND*)

(*who*) Lemma PO_10 :
((anyf   bits ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))). (*whoEND*)

Admitted.
(*who*) Section sec_6.
Parameter bits_7 : state.
Parameter e_8 : e.
Parameter anon_3 : unit.
Hypothesis Hypo_13 :
(((eq_out   bits )  bits_7 ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))).
Hypothesis Hypo_14 :
(((mirrorf   bits )  bits_7 ) 
 ((append   (nodf   (head   f )))  ((append   (tail   f ))  f0 ))).
 (*whoEND*)

Admitted.
(*who*) Lemma PO_11 :
(validf   ((append   (tail   f ))  f0 )). (*whoEND*)

(*who*) Lemma PO_12 :
((anyf   (((set   bits_7 )  (nodi   (head   f )))  white )) 
 ((append   (tail   f ))  f0 )). (*whoEND*)

Admitted.
(*who*) Section sec_5.
Parameter bits_8 : state.
Parameter e_9 : e.
Parameter anon_4 : unit.
Hypothesis Hypo_15 :
(((eq_out   (((set   bits_7 )  (nodi   (head   f )))  white ))  bits_8 ) 
 ((append   (tail   f ))  f0 )).
Hypothesis Hypo_16 :
(((mirrorf   (((set   bits_7 )  (nodi   (head   f )))  white ))  bits_8 ) 
 ((append   (tail   f ))  f0 )).
 (*whoEND*)

Admitted.
(*who*) Lemma PO_13 :
(((mirrorf   bits )  bits_8 )  ((append   f )  f0 )). (*whoEND*)

(*who*) Lemma PO_14 :
(((eq_out   bits )  bits_8 )  ((append   f )  f0 )). (*whoEND*)

Admitted.
(*who*) End sec_5. (*whoEND*)

Admitted.
(*who*) End sec_6. (*whoEND*)

(*who*) End sec_7. (*whoEND*)

(*who*) Section sec_10.
Parameter bits_9 : state.
Parameter e_10 : e.
Parameter anon_5 : unit.
Hypothesis Hypo_17 :
((anyf   bits_9 )  ((append   (tail   f ))  f0 )).
Hypothesis Hypo_18 :
(validf   ((append   (tail   f ))  f0 )).
 (*whoEND*)

(*who*) Section sec_8.
Parameter bits_10 : state.
Parameter e_11 : e.
Hypothesis Hypo_19 : (validf   f0 ).
Hypothesis Hypo_20 :
((anyf   bits_10 )  f0 ).
 (*whoEND*)

(*who*) Lemma PO_15 :
(((fst(k )  tt)  bits_10 )  e_11 ). (*whoEND*)

(*who*) End sec_8. (*whoEND*)

Admitted.
(*who*) Section sec_9.
Parameter bits_11 : state.
Parameter e_12 : e.
Parameter bits_12 : state.
Parameter e_13 : e.
Hypothesis Hypo_21 :
((((((snd(k )  tt)  bits_11 )  e_12 )  bits_12 )  e_13 )  tt).
 (*whoEND*)

(*who*) Lemma PO_16 :
(((mirrorf   bits_11 )  bits_12 )  f0 ). (*whoEND*)

(*who*) Lemma PO_17 :
(((eq_out   bits_11 )  bits_12 )  f0 ). (*whoEND*)

Admitted.
(*who*) End sec_9. (*whoEND*)

Admitted.
(*who*) End sec_10. (*whoEND*)

(*who*) End sec_11. (*whoEND*)

(*who*) End sec_12. (*whoEND*)


