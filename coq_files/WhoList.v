Set Implicit Arguments.
Require Export List.

Notation l_in := In.

Definition is_nil (a : Type) (l : list a) :=
  match l with
    | nil => true
    | cons _ _ => false
  end.

Notation Nil := nil (only parsing).
Notation "@Nil" := @nil (only parsing).
Notation Cons := cons (only parsing).
