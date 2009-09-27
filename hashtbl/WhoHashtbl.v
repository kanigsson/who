Set Implicit Arguments.
Require Import WhoArith.
Require Import WhoArray.
Require Import WhoList.
Parameter hashkey : Type.
Parameter hash : hashkey  -> int. 

Parameter h_eq_dec : 
  forall (a b : hashkey), {a = b} + {a <> b}.

Definition hl (a : Type) := list (hashkey* a).
Definition ht (a : Type) := array (hl a).
Fixpoint find (a : Type) (k : hashkey) (l : hl a) {struct l} :=
  match l with
    | nil => None
    | (k',v) :: xs => 
      if h_eq_dec k k' then Some v else 
        find k xs
  end.

Definition is_hashtbl a  (h : ht a) :=
  forall k v i, 
    0 < len h /\
    (0 <= i /\ i < len h ->
    In (k,v) (get i h) ->
    mod (hash k) (len h) = i).

Definition repr (a : Type) (h : ht a) (l : hl a) :=
  is_hashtbl h /\
  forall k, find k (get (mod (hash k) (len h)) h) = find k l.

Lemma mod_lt :
  forall i m,
    0 < m -> mod i m < m.
Proof.
  intros i m L.
  assert (m > 0) by omega.
  exact (proj2 (Z_mod_lt i m H)).
Qed.
  
Lemma find_cons : 
  forall a l1 l2 k k' (v : a),
    find k l1 = find k l2 ->
    find k ((k',v)::l1) = find k ((k',v)::l2).
Proof.
  intros a l1 l2 k k' v EQ; simpl; rewrite EQ; auto.
Qed.

Definition upd a i v (ar : array a) := set i (v (get i ar)) ar.

Lemma upd_len :
  forall a (ar : array a) i v, len (upd i v ar) = len ar.
Proof.
  intros; unfold upd; rewrite <- update_len; auto.
Qed.

Inductive HCompare (a: Type) (h1 h2 : hashkey) (ar : array a) : Type :=
  | EQ : h1 = h2 -> HCompare h1 h2 ar
  | HEQ : h1 <> h2 -> mod (hash h1) (len ar) = mod (hash h2) (len ar) 
           -> HCompare h1 h2 ar
  | NEQ : hash h1 <> hash h2 -> HCompare h1 h2 ar.

Lemma HCompare_dec :
  forall a h1 h2 (ar : array a), HCompare h1 h2 ar.
Proof.
  refine (fun a h1 h2 ar =>
    match h_eq_dec h1 h2 with
      | left e => _
      | right n =>
        match Z_eq_dec (mod (hash h1) (len ar)) 
                       (mod (hash h2) (len ar)) with
          | left e => _
          | right n => _
        end
    end).
  apply EQ; auto.
  apply HEQ; auto.
  apply NEQ; congruence.
Qed.

Lemma add_elem : 
  forall a (h : ht a) k v,
    is_hashtbl h -> is_hashtbl (upd (mod (hash k) (len h)) (cons (k,v)) h).
Proof.
  intros a h k v I.
  unfold is_hashtbl in *. intros k1 v1 i.
  assert (0 < len h) by (apply (I k v i)).
  rewrite upd_len in *; split; auto.
  intros ENCL LIN.
  case_eq (HCompare_dec k k1 h); intros.
  rewrite e in *; clear e H0.
  generalize (in_inv LIN); intros [K | K]. injection K as K2; rewrite K2 in *; clear K2 K. auto. 
  case_eq (Z_eq_dec i (mod (hash k1) (len h))); intros; auto.
  rewrite e in *; unfold upd in *; rewrite get_set_eq in LIN.
  apply (I k1 v1 i); auto.
  
    intros a h i k v IH IM k0 v0 i0. 
  rewrite <- update_len in *; split; auto.
  intros ENCL LIN.
  case_eq (Z_eq_dec i i0); intros E D.
  rewrite E in *; clear E D. rewrite get_set_eq in LIN.
  apply (IH k0 v0 i0) ; auto. intuition. 
  rewrite get_set_neq in LIN; auto. apply (IH k0 v0 i0); auto. 
  intuition. rewrite IM; apply mod_lt; auto. 
Qed.

Lemma add_elem2 : 
  forall a (h : ht a) l i k v,
    is_hashtbl h -> repr h l -> i = mod (hash k) (len h) ->
      repr (set i (cons (k,v) (get i h)) h) (cons (k,v) l).
Proof.
  unfold is_hashtbl, repr; 
  intros a h l i key v IH [R1 R2] IM. split.
  apply add_elem; auto. intros k0.
  rewrite <- update_len in *. rewrite IM in *; clear IM.
  assert (GZ : 0 < len h) by (apply (IH key v i)).
  assert (LT : mod (hash k0) (len h) < len h ) by ( apply mod_lt; auto).
  case_eq (Z_eq_dec (mod (hash k0) (len h)) (mod (hash key) (len h))); intros E D.
  rewrite <- E in *; clear E D; rewrite get_set_eq in *; auto.
  apply find_cons; apply R2. 
  rewrite get_set_neq; auto.
  simpl. case_eq (h_eq_dec k0 key); intros; auto. congruence.
  apply mod_lt; auto.
Qed.

  

