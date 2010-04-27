Parameter key : Type.
Parameter kmap : Type. 
Variable ref : forall (a : Type) (k : key), Type. 
Definition kget : forall (A : Type), key -> kmap -> A. Admitted.

Definition kset: forall (A : Type), key -> A -> kmap -> kmap. Admitted.
Definition kcombine: kmap -> kmap -> kmap . Admitted.
Definition krestrict : kmap -> kmap. Admitted.
Definition kempty : kmap. Admitted.

Notation "a -->> b" :=
  ((a -> kmap -> Prop) * 
  ( a -> kmap -> kmap -> b -> Prop))%type ( at level 200).

Definition ifp (a : Type) : Prop -> a -> a -> a. Admitted.

Axiom ifp_true :
  forall a (p : Prop) l r, p -> ifp a p l r = l.
Axiom ifp_false :
  forall a (p : Prop) l r, ~ p -> ifp a p l r = l.