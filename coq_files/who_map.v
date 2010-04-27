Require Import FunctionalExtensionality.
Require Import Bool.
Require Import Setoid.
Open Scope bool_scope.

Definition ifp (a : Type) : Prop -> a -> a -> a. Admitted.


Module Type Map.
  Parameter key : Type.
  Parameter kdec : forall (a b : key), {a = b} + {a <> b}.
  Parameter value : Type.
  Parameter kset : Type.
  Parameter kmap : Type.

  Parameter get : key -> kmap -> option value.
  Parameter set : key -> value -> kmap -> kmap.
  Parameter domain : kmap -> kset.
  Parameter union : kset -> kset -> kset.
  Parameter add : key -> kset -> kset.
  Parameter empty : kmap.
  Parameter sempty : kset.
  Parameter combine : kmap -> kmap -> kmap.
  Parameter restrict : kset -> kmap -> kmap.
  Parameter intersection : kset -> kset -> kset.
  
  Parameter mem : key -> kset -> bool.
  
  Notation "a `in b" := (mem a b) (at level 73).
  Notation "a |+| b" := (combine a b) (at level 74).
  Notation "a # b" := (intersection a b = sempty) (at level 75).
  Notation "a ## b" := ((domain a) # (domain b)) (at level 76).

  Axiom dom_def :
    forall x m,
      ( x `in domain m) = 
      match get x m with
        | Some v => true
        | None => false
     end.

  Axiom dom_set : 
    forall x y v m,
      (y `in domain (set x v m)) =
      if kdec x y then true else y `in domain m.

  Axiom get_set :
  forall x y v m,
    get x (set y v m) =
    if kdec x y then Some v else get x m.

  Axiom ext_eq_map :
  forall m1 m2,
    (forall x, get x m1 = get x m2) -> m1 = m2.

  Axiom eq_ext_map :
  forall m1 m2,
    m1 = m2 <-> (forall x, get x m1 = get x m2).

  Axiom ext_eq_set : 
    forall s1 s2,
      (forall x, mem x s1 = mem x s2) -> s1 = s2.

  Axiom eq_ext_set : 
    forall s1 s2,
      s1 = s2 <-> (forall x, mem x s1 = mem x s2). 

  Axiom combine_get :
  forall m1 m2 x,
    get x (m1 |+|  m2) = 
    if x `in domain m2 then get x m2 else get x m1.

  Axiom union_def :
    forall k s1 s2,
      mem k (union s1 s2) =
      mem k s1 || mem k s2.

  Axiom restrict_def :
    forall k s m,
      get k (restrict s m) =
      if mem k s then get k m else None.

  Axiom intersection_def :
    forall s1 s2 x,
      (x `in (intersection s1 s2)) =
      if mem x s1 then mem x s2 else false.

  Axiom sempty_def :
    forall k, (k `in sempty) = false.

  Axiom empty_def :
    forall k, get k empty = None.

  Axiom add_def :
    forall k x s, mem k (add x s) = if kdec x k then true else mem k s.

End Map.

Module MapFacts (Import M : Map).

  Lemma set_exchange :
    forall x v y u m,
      set x v (set y u m) = 
        if kdec x y then set x v m else set y u (set x v m).
  Proof.
    intros x v y u m. apply M.ext_eq_map; intro z.
    case_eq (kdec x y); intros.
    do 3 rewrite get_set.
    case_eq (kdec z x); intros; case_eq (kdec z y); intros; auto.
    assert (z = x) by (transitivity y; auto); contradiction.
    do 4 rewrite get_set.
    case_eq (kdec z x); intros; case_eq (kdec z y); intros; auto.
    assert (x = y) by (transitivity z; auto); contradiction.
  Qed.
  
  Lemma combine_dom : 
  forall m1 m2,
    domain (m1 |+| m2) = union (domain m1) (domain m2).
  Proof.
    intros m1 m2; apply ext_eq_set; intro z.
    rewrite dom_def, combine_get, union_def.
    case_eq (z `in domain m2); intros A.
    case_eq (get z m2); intros B. intros;
    symmetry; apply orb_true_r.
    generalize (dom_def z m2); intro C;
    rewrite A,B in C; discriminate.
    case_eq (z `in domain m1); case_eq (get z m1);intros; auto;
    generalize (dom_def z m1); intro C; rewrite H, H0 in C;
      discriminate.
  Qed.

  Lemma restrict_dom : 
    forall m p x,
      (x `in domain (restrict p m)) = (x `in domain m) && mem x p.
  Proof.
    intros m p x;
    rewrite dom_def, restrict_def.
    case_eq (x `in p); intros.
    rewrite dom_def; case_eq (get x m); intros; auto.
    symmetry; apply andb_false_r.
  Qed.

  Lemma restrict_combine : 
  forall m1 m2 s,
    restrict s (m1 |+| m2) =
    ((restrict s m1) |+| (restrict s m2)).
  Proof.
   intros m1 m2 s; apply ext_eq_map; intro z.
   rewrite restrict_def, combine_get, combine_get, restrict_def,
     restrict_def, restrict_dom.
   case_eq (z `in s); intro A.
   rewrite (andb_true_r). reflexivity.
   case_eq ((z `in domain m2) && false); auto.
  Qed.
 
 Ltac maprew := 
  repeat (rewrite ?restrict_def, ?union_def, ?combine_get, ?dom_def,
     ?intersection_def, ?empty_def, ?sempty_def, ?add_def in *).


  Lemma same_base :
  forall m s,
    m = (m |+| restrict s m).
  Proof.
    intros m s; apply ext_eq_map; intro z; maprew.
    case_eq (z `in s); intro A; auto.
    case_eq (get z m); intros; auto.
  Qed.

  Lemma same_base_2 : 
    forall m s1 s2,
      (restrict s1 m |+| restrict s2 m) =
        restrict (union s1 s2) m.
  Proof.
   intros m s1 s2. apply ext_eq_map; intro z; maprew.
   case_eq (z `in s2); intros.
   case_eq (get z m); intros;
   case_eq (z `in s1); intros; auto.
   rewrite orb_false_r; auto.
  Qed.

  Definition subset s1 s2 :=
    forall x, (if mem x s1 then mem x s2 else true) = true.

  Lemma restrict_elim :
    forall m s, subset (domain m) s ->
      restrict s m = m.
  Proof.
    unfold subset; intros m s H; apply ext_eq_map; intro z; generalize (H z); 
    clear H; maprew; intro H.
    case_eq (z `in s); intros; auto.
    case_eq (get z m); intros; auto. rewrite H1 in H; simpl in *.
    rewrite H in H0; discriminate. 
  Qed.

  Lemma subset_refl :
    forall s, subset s s.
  Proof.
    intros s x; case_eq (mem x s); intros; auto.
  Qed.

  Lemma restrict_combine_right : 
    forall m1 m2 s,
      subset s (domain m2) ->
      restrict s (m1 |+| m2) = restrict s m2.
  Proof.
    intros m1 m2 s S.
    apply ext_eq_map; intros; maprew.
    case_eq (x `in s); intro B; auto.
    case_eq (get x m2); intro C; auto. 
    unfold subset in S. generalize (S x); rewrite B,dom_def, C; intros D.
    discriminate.
  Qed.
  
  Lemma restrict_combine_left : 
    forall m1 m2 s,
      s # (domain m2) ->
      restrict s (m1 |+| m2) = restrict s m1.
  Proof.
    intros m1 m2 s S. apply ext_eq_map; intros; maprew.
    case_eq (x `in s); intro B; auto.
    case_eq (get x m2); intro C; auto.
    intros X. 
    assert ((x `in sempty) = true).
    rewrite <- S. rewrite intersection_def. rewrite B. rewrite dom_def. rewrite X. auto.
    rewrite sempty_def in H. discriminate.
  Qed.

End MapFacts.

Module FuMap : Map.
  Parameter key : Type.
  Parameter kdec : forall (a b : key), { a = b } + {a <> b}.
  Parameter value : Type.
  Definition kset := key -> bool.
  Definition kmap := key -> option value.
  Definition get (x : key) (m : kmap) := m x.
  Definition mem (x : key) ( s : kset) := s x.
  Definition domain (m : kmap) (z : key) :=
    match get z m with
    | None => false
    | Some _ => true
   end.

  Definition set (x : key) (v : value) (m : kmap) (z : key) :=
    if kdec z x then Some v else get z m.

  Definition union (s1 s2: kset) (z : key) :=
    if mem z s1 then true else mem z s2.

  Definition add x (s : kset) z :=
    if kdec x z then true else mem z s.

  Definition intersection (s1 s2 : kset) (z : key) :=
    if mem z s1 then mem z s2 else false.

  Definition empty : kmap := fun z => None.
  Definition sempty (z : key) := false.

  Definition combine (m1 m2 : kmap) (z : key) :=
    match get z m2 with
    | None => get z m1
    | Some v => Some v
   end.

  Definition restrict (s : kset) (m : kmap) (x : key) :=
    if mem x s then get x m else None.

  Notation "a `in b" := (mem a b) (at level 73).
  Notation "a |+| b" := (combine a b) (at level 74).

  Ltac munf := unfold restrict,combine,union,domain,set,get,mem.

  Lemma dom_def :
    forall x m,
      ( x `in domain m) = 
      match get x m with
        | Some v => true
        | None => false
      end.
  Proof. reflexivity. Qed.

  Lemma dom_set : 
    forall x y v m,
      (y `in domain (set x v m)) =
      if kdec x y then true else y `in domain m.
  Proof.
    intros x y v m; munf.
    case_eq (kdec y x); intros; case_eq (kdec x y);
      intros; auto. 
    assert (x = y) by auto; contradiction.
  Qed.
      
  Lemma get_set :
  forall x y v m,
    get x (set y v m) =
    if kdec x y then Some v else get x m.
  Proof. reflexivity. Qed.
 
  Lemma ext_eq_map :
  forall m1 m2,
    (forall x, get x m1 = get x m2) -> m1 = m2.
  Proof.
    munf. apply functional_extensionality. Qed.

  Lemma ext_eq_set : 
    forall s1 s2,
      (forall x, mem x s1 = mem x s2) -> s1 = s2.
  Proof. munf; apply functional_extensionality. Qed.

  Lemma combine_get :
  forall m1 m2 x,
    get x (m1 |+|  m2) = 
    if x `in domain m2 then get x m2 else get x m1.
  Proof.
    munf; intros m1 m2 x.
    case_eq (m2 x); intros; auto.
  Qed.

  Lemma union_def :
    forall k s1 s2,
      mem k (union s1 s2) =
      mem k s1 || mem k s2.
  Proof. reflexivity. Qed.

  Lemma restrict_def :
    forall k s m,
      get k (restrict s m) =
      if mem k s then get k m else None.
  Proof. reflexivity. Qed.

  Lemma intersection_def :
    forall s1 s2 x,
      (x `in (intersection s1 s2)) =
      if mem x s1 then mem x s2 else false.
  Proof. reflexivity. Qed.

  Lemma empty_def :
    forall k, get k empty = None.
  Proof. reflexivity. Qed.

  Lemma sempty_def :
    forall k, mem k sempty = false.
  Proof. reflexivity. Qed.

  Lemma add_def : 
    forall k x s, mem k (add x s) = if kdec x k then true else mem k s.
  Proof. reflexivity. Qed.

  Lemma eq_ext_map :
  forall m1 m2,
    m1 = m2 <-> (forall x, get x m1 = get x m2).
  Proof.
    intros m1 m2;split; intuition. rewrite H; auto.
    apply ext_eq_map; auto.
  Qed.

  Lemma eq_ext_set : 
    forall s1 s2,
      s1 = s2 <-> (forall x, mem x s1 = mem x s2). 
  Proof. intros s1 s2; split. intros EQ k; rewrite EQ; auto. 
    intros x; apply ext_eq_set; auto. Qed.

End FuMap.

Module K := MapFacts(FuMap).

Export FuMap.
Export K.

Lemma PO_10 : 
  forall m1 m2 s1 s2 s3,
    domain m1 = union s1 (union s2 s3) ->
    domain m2 = union s1 s3 ->
    s2 # s3 -> s1 # s3 -> s1 # s2 ->
    restrict (union s1 s2) (m1 |+| (restrict s1 m2))
    = restrict (union s1 s2) (m1 |+| m2).
Proof.
  intros m1 m2 s1 s2 s3 D1 D2 DJ1 DJ2 DJ3; apply ext_eq_map; intro z.
  maprew. 
  case_eq (z `in s1); intros; auto.
  case_eq (z `in s2); intros; simpl; auto.
  case_eq (get z m2); intros; auto.
  assert ((z `in domain m2) = true).
  maprew; rewrite H1; auto.
  rewrite D2 in H2; maprew.
  rewrite H in H2; simpl in H2.
  assert ((z `in intersection s2 s3) = true).
  maprew. rewrite H0, H2; auto.
  rewrite DJ1 in H3. maprew. discriminate.
Qed.

