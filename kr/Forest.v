
Require Export Arith.
Require Export Peano_dec.
Require Export Wf_nat.
Require Export Omega.

(** Trees and forests. *)

Inductive tree : Set :=
  | Node : nat -> forest -> tree

with forest : Set :=
  | Fnil : forest
  | Fcons : tree -> forest -> forest.

Scheme tree_forest_ind := Induction for tree Sort Prop 
with forest_tree_ind := Induction for forest Sort Prop.

Definition is_nil (f:forest) : bool := match f with
  | Fnil => true
  | Fcons _ _ => false end.

Hint Unfold is_nil.

Definition nodi (t:tree) : nat := match t with
  | Node i _ => i end.

Definition nodf (t:tree) : forest := match t with
  | Node _ f => f end.

Definition head (f:forest) : tree := match f with
  | Fnil => Node 0 Fnil (* absurd *)
  | Fcons t _ => t end.

Definition tail (f:forest) : forest := match f with
  | Fnil => Fnil
  | Fcons _ f => f end.

(** Concatenation of two forests. *)

Fixpoint append (f:forest) : forest -> forest :=
  fun f0:forest => match f with 
               Fnil => f0
             | (Fcons t f') => (Fcons t (append f' f0)) end.

(** Size of trees and forests. *)

Fixpoint sizef (f:forest) : nat :=
  match f with Fnil => O 
           | (Fcons t f') => (plus (sizet t) (sizef f')) end

with sizet (t:tree) : nat :=
  match t with (Node _ f) => (S (sizef f)) end.

(*i Concatenation of a tree at the end of a forest.

Fixpoint appendt [f:forest] : tree -> forest :=
  [t:tree]Cases f of
            Fnil => (Fcons t Fnil)
          | (Fcons t' f') => (Fcons t' (appendt f' t)) end.
i*)

(** Occurrence of an index [i] in a tree ([int]) and in a forest ([inf]). *)

Inductive int (i:nat) : tree -> Prop :=
  | int_root : forall (f:forest), (int i (Node i f))
  | int_sons : forall (j:nat)(f:forest), (inf i f) -> (int i (Node j f))

with inf (i:nat) : forest -> Prop := 
  | inf_hd : forall (t:tree)(f:forest), (int i t) -> (inf i (Fcons t f))
  | inf_tl : forall (t:tree)(f:forest), (inf i f) -> (inf i (Fcons t f)).

Hint Resolve int_root int_sons inf_hd inf_tl.

(** Lemmas on [inf]. *)

Lemma inf_in_append_1 : forall (f f0:forest)(i:nat),
  (inf i f) -> (inf i (append f f0)).
Proof.
induction f; simpl.
intros; inversion H; auto.
intros; inversion H; auto.
Save.

Lemma inf_in_append_2 : forall (f f0:forest)(i:nat),
  (inf i f0) -> (inf i (append f f0)).
Proof.
induction f; simpl; auto.
Save.

Lemma inf_append : forall (f f0:forest)(i:nat),
  (inf i (append f f0)) -> (inf i f) \/ (inf i f0).
Proof.
induction f; simpl; intros; auto.
inversion H; intuition.
elim (IHf f0 i H1); auto.
Save.

Lemma inf_append_inv : forall f f0 i, 
  inf i (append f f0) -> inf i f \/ inf i f0.
Admitted.

Hint Resolve inf_in_append_1 inf_in_append_2 inf_append.

(** The property for two forests not to have indexes in common. *)

Definition disjoint (f f':forest) : Prop := 
  forall i, inf i f -> inf i f' -> False.

Lemma disjoint_sym : forall f1 f2, disjoint f1 f2 -> disjoint f2 f1.
Admitted.

Hint Resolve disjoint_sym.

(*i A technical lemma about [appendt]:
    if [t::f = appendt f' t'] with [~f'=Fnil] then
    there exists a forest [f''] such that [f'=t::f''] and [f=appendt f'' t'].

Lemma cons_eq_appendt : 
  (t,t':tree)(f':forest) ~f'=Fnil -> (f:forest) (Fcons t f)=(appendt f' t') ->
  (EX f'':forest | f'=(Fcons t f'') & f=(appendt f'' t')).
Proof.
induction f'.
Intro H; elim H; Reflexivity.
intros.
Exists f.
simpl in H1. Injection H1.
intros eqf eqt; rewrite eqt; Reflexivity.
simpl in H1. Injection H1.
Trivial.
Save.
i*)

(*s If index [i] occurs in [t] or [f], it occurs in [f@t]. *)

(*i
Lemma inf_in_appendt : (t:tree)(f:forest)(i:nat)
  (inf i f) -> (inf i (appendt f t)).
Proof.
induction f; simpl; auto.
intros; inversion H0; auto.
Save.

Lemma int_in_appendt : (t:tree)(f:forest)(i:nat)
  (int i t) -> (inf i (appendt f t)).
Proof.
induction f; simpl; auto.
Save.

Hints Resolve inf_in_appendt int_in_appendt.
i*)

(*i
Proof.
intros until f; pattern f; apply forest_tree_ind with
  P := [t:tree]Cases t of (Node i f') => 
      ((i:nat)(inf i f') -> (s' i)=(s i)) -> (F s f') -> (F s' f') end.
auto.
auto.
intros.
inversion H2; intros; auto.
apply f_odd; auto.
unfold Z; unfold Z in H4; intros.
rewrite H1; auto.
rewrite <- H3; auto.
rewrite H1; auto.
rewrite <- H3; auto.
i*)

(** The nullity of a forest is decidable. *)

Lemma dec_is_Fnil : forall (f:forest), f=Fnil \/ ~f=Fnil.
Proof.
intro f; case f; [ auto | right; discriminate ].
Save.

Lemma append_nil : forall (f f0:forest),
  (append f f0)=Fnil -> f=Fnil /\ f0=Fnil.
Proof.
induction f; simpl; intuition.
intros; discriminate H.
discriminate H.
Save.

(*i [appendt f t] is not [Fnil].

Lemma appendt_is_not_nil : (f:forest)(t:tree)~(appendt f t)=Fnil.
Proof.
induction f; simpl; intros; Discriminate.
Save.

Hints Resolve appendt_is_not_nil.
i*)

(*i [appendt] is injective.

Lemma appendt_eq_appendt : (f,f':forest)(t,t':tree)
  (appendt f t)=(appendt f' t') -> f=f' /\ t=t'.
Proof.
induction f; simpl; intros.
induction f'; simpl; intros.
simpl in H. Injection H. auto.
simpl in H. Injection H.
intros; elim (appendt_is_not_nil f' t' (sym_eq ? ? ? H0)).
induction f'; simpl; intros; simpl in H0; Injection H0; intros.
elim (appendt_is_not_nil f0 t0 H1).
rewrite H2. 
elim (H f' t0 t' H1); intros.
split; Try assumption. apply (f_equal ? ? (Fcons t1)). Eauto.
Save.

Hints Resolve appendt_eq_appendt.
i*)

(** Length of a forest (i.e. number of trees). *)

Fixpoint lengthf (f:forest) : nat :=
  match f with Fnil => O | (Fcons _ f') => (S (lengthf f')) end.

(*i The length of of [f] is less than the length of [appendt f t].

Lemma lt_length_appendt : (f:forest)(t:tree)(lt (lengthf f) (lengthf (appendt f t))).
Proof.
induction f; simpl; auto.
intros. apply lt_n_S. apply H.
Save.
i*)

(** Validity. A tree/forest is valid if all its nodes are different. *)

Inductive validt : tree -> Prop :=
| validt_node : forall i f, ~(inf i f) -> validf f -> validt (Node i f)

with validf : forest -> Prop :=
| validf_nil  : validf Fnil
| validf_cons : forall t f, validt t -> validf f -> 
                (forall i, int i t -> inf i f -> False) -> validf (Fcons t f).

Hint Resolve validt_node validf_nil validf_cons.

Lemma valid_cons : forall t f, validf (Fcons t f) -> validf f.
Proof.
  inversion 1; intuition.
Qed.

Lemma valid_cons_node : 
  forall i f1 f2, validf (Fcons (Node i f1) f2) -> validf (append f1 f2).
Proof.
  induction f1; simpl.
  inversion 1; auto.
  intros; apply validf_cons.
  inversion H; intuition.
  inversion H2; intuition.
  inversion H8; intuition.
  apply IHf1; clear IHf1.
  (*TODO*)
Admitted.

Hint Resolve valid_cons valid_cons_node.

Lemma validf_not_inf : forall n f1 f2,
  validf (Fcons (Node n f1) f2) ->  ~(inf n (append f1 f2)).
Admitted.

Hint Resolve validf_not_inf.

Lemma validf_disjoint: forall n f1 f2,
  validf (Fcons (Node n f1) f2) ->  disjoint f1 f2.
Admitted.

Hint Resolve validf_disjoint.

