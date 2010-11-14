
Require Export Forest.

(** Parity of a forest. This is the parity of $N(f)$, the number of
    its colorings. *)

Inductive evenf : forest -> Prop :=
  | even_cons_hd : forall t f, event t -> evenf (Fcons t f)
  | even_cons_tl : forall t f, evenf f -> evenf (Fcons t f)

with oddf : forest -> Prop :=
  | odd_nil : oddf Fnil
  | odd_cons : forall t f, oddt t -> oddf f -> oddf (Fcons t f)

with event : tree -> Prop :=
  | event_node : forall i f, oddf f -> event (Node i f)

with oddt : tree -> Prop :=
  | oddt_node : forall i f, evenf f -> oddt (Node i f).

Hint Constructors evenf oddf event oddt.

(** A forest is either [even] or [odd]. *)

Lemma dec_even_odd_t : forall (t:tree), (event t)\/(oddt t).
Admitted.

Lemma dec_even_odd : forall (f:forest), (evenf f)\/(oddf f).
Proof.
intro f; pattern f; apply forest_tree_ind with 
  (P:=fun (t:tree) => match t with (Node _ f) => (evenf f)\/(oddf f) end); auto.
intro t; case t; intuition.
Save.

Lemma absurd_even_odd_t : forall t, event t -> oddt t -> False.
Admitted.

Lemma absurd_even_odd_f : forall (f:forest), (evenf f) -> (oddf f) -> False.
Proof.
intros until f; pattern f.
apply (@well_founded_ind forest (ltof forest sizef)).
apply well_founded_ltof.
clear f; intros f Hrec H H0.
induction f; intuition.
inversion H.
clear IHf; inversion H.
subst. inversion H0.
(***
apply (Hrec f'); auto.
rewrite <- H1; unfold ltof; simpl; omega.
inversion H0.
apply (Hrec f); auto.
rewrite <- H4; unfold ltof; simpl; omega.
Save.
***)
Admitted.

Hint Resolve dec_even_odd absurd_even_odd_t absurd_even_odd_t.

(** Colors are [Black] and [White] and a state is a coloring of nodes
    (a mapping from [nat] to [color]). *)

Inductive color : Set := Black : color | White : color.

Definition is_white (c:color) : bool :=
  match c with Black => false | White => true end.

(** States *)

Definition state := nat -> color.

Definition get (s:state) (i:nat) := s i.

Definition set (s:state) (i:nat) (c:color) :=
  fun (j:nat) => match (eq_nat_dec i j) with
           (left _) => c 
         | (right _) => (s j) end.

(** [eq_in s s' f] means that [s] and [s'] coincide on the nodes of [f]
     [eq_out s s' f] means that [s] and [s'] coincide on the nodes not in [f] *)

Definition eq_in (s s':state) f := forall i, inf i f -> s' i = s i.

Definition eq_out (s s':state) f := forall i, ~(inf i f) -> s' i = s i.

Lemma eq_in_eq_out : 
  forall s s' f1 f2, eq_out s s' f1 -> disjoint f1 f2 -> eq_in s s' f2.
Admitted.

Hint Unfold eq_in eq_out.
Hint Resolve eq_in_eq_out.

Lemma eq_in_append : forall (s s':state)(f f0:forest),
  (eq_in s s' f) -> (eq_in s s' f0) -> (eq_in s s' (append f f0)).
Proof.
unfold eq_in; induction f; simpl; intuition.
intros; inversion H1; eauto.
Save.

Lemma eq_in_append_1 : forall (s s':state)(f f':forest),
 (eq_in s s' (append f f')) -> (eq_in s s' f).
Proof.
 intuition.
Save.

Lemma eq_in_append_2 : forall (s s':state)(f f':forest),
 (eq_in s s' (append f f')) -> (eq_in s s' f').
Proof.
intuition.
Save.

Lemma eq_in_trans : forall s s' s'' f,
  eq_in s s' f -> eq_in s' s'' f -> eq_in s s'' f.
Admitted.

Hint Resolve eq_in_append eq_in_append_1 eq_in_append_2 eq_in_trans.

Lemma eq_out_trans : forall s s' s'' f,
  eq_out s s' f -> eq_out s' s'' f -> eq_out s s'' f.
Admitted.

Hint Resolve eq_out_trans.

(** [frame P] states that [P] is a property over a state and a forest
     which only depends on the nodes of the forest. *)

Definition frame (P:state -> forest -> Prop) :=
  forall s f, P s f -> forall s', eq_in s s' f -> P s' f.

Lemma frame_eq_out : forall P,
  frame P -> forall s s' f1 f2, eq_out s s' f1 -> disjoint f1 f2 -> P s f2 -> P s' f2.
Admitted.

(** Initial state: all nodes are white. *)

Definition It (s:state) (t:tree) : Prop :=
  forall (i:nat), (int i t) -> (s i)=White.

Definition If (s:state) (f:forest) : Prop :=
  forall (i:nat), (inf i f) -> (s i)=White.

Hint Unfold It If.

(** Lemmas over [If]. *)

(*i
Lemma I_appendt : (s:state)(f0:forest)(i:nat)(f:forest)
  (I s f0) -> (s i)=White -> (I s f) -> (I s (appendt f0 (Node i f))).
Proof.
unfold I; induction f0; simpl; intros.
inversion H2; auto.
inversion H4; auto.
inversion H3; auto.
apply H with f0:=f1 i:=i; auto.
Save.
i*)

Lemma If_append_1 : forall (s:state)(f f0:forest),
  (If s (append f f0)) -> (If s f).
Proof.
intuition.
Save.

Lemma If_append_2 : forall (s:state)(f f0:forest),
  (If s (append f f0)) -> (If s f0).
Proof.
intuition.
Save.

Lemma If_cons : forall (s:state)(f0:forest)(i:nat)(f:forest),
  (If s f0) -> (s i)=White -> (If s f) -> (If s (Fcons (Node i f) f0)).
Proof.
unfold If; intuition.
intros; inversion H2; auto.
inversion H4; auto.
Save.

Lemma If_Fnil : forall (s:state), (If s Fnil).
Proof.
unfold If; intros; inversion H.
Save.

Lemma If_append : forall (s:state)(f f0:forest),
  (If s f) -> (If s f0) -> (If s (append f f0)).
Proof.
unfold If; intros.
elim (inf_append f f0 i); auto.
Save.

Lemma If_cons_inv : forall (s:state)(f0:forest)(i:nat)(f:forest),
  (If s (Fcons (Node i f) f0)) -> (If s f0) /\ (s i)=White /\ (If s f).
Proof.
intuition.
Save.

Lemma If_cons_inv_1 : forall (s:state)(f0:forest)(i:nat)(f:forest),
  (If s (Fcons (Node i f) f0)) -> (If s f).
Proof.
intuition.
Save.

Lemma If_cons_inv_3 : forall (s:state)(f0:forest)(i:nat)(f:forest),
  (If s (Fcons (Node i f) f0)) -> (If s f0).
Proof.
intuition.
Save.

Hint Resolve If_append_1 If_append_2 If_cons If_Fnil If_append
              If_cons_inv_1 If_cons_inv_3.

(** Final state. *)

Inductive Ff (s:state) : forest -> Prop :=
  | ff_nil : Ff s Fnil
  | ff_odd : forall t f, Ft s t -> event t -> If s f -> Ff s (Fcons t f)
  | ff_even : forall t f, Ft s t -> oddt t -> Ff s f -> Ff s (Fcons t f)

with Ft (s:state) : tree -> Prop :=
  | ft_node : forall i f, s i = Black -> Ff s f -> Ft s (Node i f).

Hint Constructors Ft Ff.

(** Lemmas on [F]. *)

Lemma Ff_append : forall (s:state)(f f0:forest),
   ((evenf f) -> (Ff s f) -> (If s f0) -> (Ff s (append f f0)))
/\ ((oddf f) -> (Ff s f) -> (Ff s f0) -> (Ff s (append f f0))).
Proof.
induction f; simpl; split; intros.
inversion H.
assumption.
(***
inversion H; subst.
inversion H; subst.
apply f_odd; auto.
elim (absurd_even_odd f'); auto.
inversion H; subst.
apply f_odd; auto.
apply f_even; auto.
elim (H f1); auto.
inversion H0.
rewrite <- H3 in H1; inversion H1.
elim (absurd_even_odd f'); auto.
apply f_even; auto.
elim (H f1); auto.
Save.
***)
Admitted.

Lemma Ff_append_even : forall (s:state)(f f0:forest),
  (evenf f) -> (Ff s f) -> (If s f0) -> (Ff s (append f f0)).
Proof.
intros s f f0; exact (proj1  (Ff_append s f f0)).
Save.

Lemma Ff_append_odd : forall (s:state)(f f0:forest),
  (oddf f) -> (Ff s f) -> (Ff s f0) -> (Ff s (append f f0)).
Proof.
intros s f f0; exact (proj2 (Ff_append s f f0)).
Save.

Hint Resolve Ff_append Ff_append_even Ff_append_odd.

Lemma Ff_append_inv : forall (s:state)(f f0:forest),
  (Ff s (append f f0)) -> 
  (Ff s f) /\ (   ((evenf f) /\ (If s f0))
              \/ ((oddf f) /\ (Ff s f0))).
Proof.
induction f; simpl; intros.
auto.
split.
inversion H; subst.
apply ff_odd; eauto.
apply ff_even; eauto.
elim (IHf f0 H4); auto.
inversion H; subst.
left; eauto.
elim (dec_even_odd f); intro.
left; split; eauto.
elim (IHf f0 H4); intuition.
elim (absurd_even_odd_f f); auto.
right; split; eauto.
elim (IHf f0 H4); intuition.
elim (absurd_even_odd_f f); auto.
Save.

Lemma Ff_append_inv_1 : forall (s:state)(f f0:forest),
  (Ff s (append f f0)) -> (Ff s f).
Proof.
intros; elim Ff_append_inv with (s:=s) (f:=f) (f0:=f0); intuition.
Save.

Lemma Ff_append_even_inv_1 : forall (s:state)(f f0:forest),
  (Ff s (append f f0)) -> (evenf f) -> (If s f0).
Proof.
intros; elim Ff_append_inv with (s:=s) (f:=f) (f0:=f0); intuition.
elim (absurd_even_odd_f f); auto.
Save.

Lemma Ff_append_odd_inv_1 : forall (s:state)(f f0:forest),
  (Ff s (append f f0)) -> (oddf f) -> (Ff s f0).
Proof.
intros; elim Ff_append_inv with (s:=s)  (f:=f) (f0:=f0); intuition.
elim (absurd_even_odd_f f); auto.
Save.

Hint Resolve Ff_append_inv_1 Ff_append_even_inv_1 Ff_append_odd_inv_1.

(** [Ff s f] is invariant if the portion of the forest [f] is 
    left unchanged in [s]. *)

Lemma frame_Ff : frame Ff.
Admitted.


(*i A lemma on [F]: if [F (t::f)] then [F f].

Lemma F_cons : (s:state)(f:forest)(t:tree)(F s (Fcons t f)) -> (F s f).
Proof.
intros until f; pattern f.
apply (well_founded_ind forest (ltof forest lengthf)).
apply well_founded_ltof.
clear f; intros f Hrec t H.
elim (dec_is_Fnil f); Intro Hf.
rewrite Hf; auto.
inversion H.  
elim (cons_eq_appendt t (Node i f1) f0) with f:=f.
intros. rewrite H6. apply f_odd; Try assumption.
unfold Z. unfold Z in H1.
intros; apply H1. rewrite H5. auto.
Red; Intro. rewrite H5 in H0; simpl in H0. apply Hf. inversion H0. Reflexivity.
auto.
elim (cons_eq_appendt t (Node i f1) f0) with f:=f.
intros. rewrite H6. apply f_even; Try assumption.
apply Hrec with t:=t. unfold ltof.
rewrite H6. apply lt_length_appendt.
rewrite <- H5; assumption.
Red; Intro. rewrite H5 in H0; simpl in H0. apply Hf. inversion H0. Reflexivity.
auto.
Save.

Hints Resolve F_cons.
i*)

(** [I] and [F] are exclusive *)

Lemma If_Ff_exclusion : forall (f:forest)(s:state),
  (If s f) -> (Ff s f) -> f=Fnil.
Proof.
induction f; simpl; intuition; intros.
inversion H0; subst.
(***
  (cut ((s i)=White);
  [ intro Hsi; rewrite Hsi in H5; discriminate H5 |
    apply H; (*rewrite <- H1;*) auto ]).
Save.
***)
Admitted.

Hint Resolve If_Ff_exclusion.

(** An acceptable state for a tree is either initial or final.
     An acceptable state for a forest is to have all of its trees in acceptable states. *)

Definition anyt (s:state) (t:tree): Prop := 
   It s t \/ Ft s t.

Inductive anyf (s:state) : forest -> Prop :=
  | anyf_nil : anyf s Fnil
  | anyf_cons: forall t f, anyt s t -> anyf s f -> anyf s (Fcons t f).

Hint Unfold anyt.
Hint Constructors anyf.

(** Lemma on [anyf] *)

Lemma any_cons : forall (t:tree)(f:forest)(s:state),
  (anyf s (Fcons t f)) -> (anyf s f).
Proof.
intros; inversion H; assumption.
Save.

Lemma any_append : forall (s:state)(f f':forest),
  (anyf s f) -> (anyf s f') -> (anyf s (append f f')).
Proof.
induction f; simpl; auto.
induction t; intros; inversion H; auto. 
Save.

Lemma If_is_any : forall (s:state)(f:forest), (If s f) -> (anyf s f).
Proof.
induction f; intuition.
induction t; intros.
apply anyf_cons; auto.
unfold anyt; left; auto.
Save.

Hint Resolve any_cons any_append If_is_any.

Lemma Ff_is_any : forall (s:state)(f:forest), (Ff s f) -> (anyf s f).
Proof.
induction f; intuition.
induction t; intros; inversion H; 
apply anyf_cons; unfold anyt; auto.
Save.

Hint Resolve Ff_is_any.

Lemma frame_anyf : frame anyf.
Admitted.



(** A state is mirrored: [I] becomes [F] and [F] becomes [I]. *)

Definition mirrort (s s':state) (t:tree) : Prop := 
    (It s t -> Ft s' t) /\ (Ft s t -> It s' t).

Inductive mirrorf (s s':state) : forest -> Prop :=
  | mirrorf_nil : mirrorf s s' Fnil
  | mirrorf_even: forall t f,
                 mirrort s s' t -> oddt t -> mirrorf s s' f ->
		 mirrorf s s' (Fcons t f)
  | mirrorf_odd : forall t f,
                 mirrort s s' t -> event t -> eq_in s s' f ->
		 mirrorf s s' (Fcons t f).

Hint Constructors mirrorf.

(** Lemmas on [mirrorf]. *)

Lemma mirrorf_append_1 : forall (s s':state)(f f':forest),
 (mirrorf s s' (append f f')) -> (mirrorf s s' f).
Proof.
induction f; simpl; auto; intros.
inversion H; intuition.
apply mirrorf_even; unfold mirrort; eauto.
Save.

Lemma mirrorf_append_2 : forall (s s':state)(f f':forest),
 (mirrorf s s' (append f f')) -> (evenf f) -> (eq_in s s' f').
Proof.
induction f; simpl; auto; intros.
inversion H0; intuition.
inversion H; subst; eauto.
inversion H0; subst; auto.
elim (absurd_even_odd_t t); auto.
Save.

Lemma mirrorf_append_3 : forall (s s':state)(f f':forest),
 (mirrorf s s' (append f f')) -> (oddf f) -> (mirrorf s s' f').
Proof.
induction f; simpl; auto; intros.
inversion H; subst.
inversion H0; subst; intuition.
inversion H0; subst; intuition.
elim (absurd_even_odd_t t); auto.
Save.

Hint Resolve mirrorf_append_1 mirrorf_append_2 mirrorf_append_3.

Lemma mirrorf_trans_1 : forall s1 s2 s3 f,
  eq_in s1 s2 f -> mirrorf s2 s3 f -> mirrorf s1 s3 f.
Admitted.

Lemma anyf_mirrorf : forall s s' f,
  anyf s f -> mirrorf s s' f -> anyf s' f.
Admitted.

Hint Resolve anyf_mirrorf.

Lemma mirror_If_Ff : forall s s' f, mirrorf s s' f -> If s f -> Ff s' f.
Proof.
  induction f; intuition.
Admitted.
