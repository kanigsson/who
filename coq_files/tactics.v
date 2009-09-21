Require Import who_map.

Ltac Case_eq t :=
  let vname := fresh "EQ" in
  let A := fresh "A" in
  case_eq t; try intros A vname; try intros vname; try rewrite vname in *.

Ltac app_set_ext z :=
  repeat
    match goal with
      | H : @eq kset ?a ?b |- _ => rewrite eq_ext_set in H; generalize (H z); clear H; intro H
      | _ => idtac
    end .

Ltac app_ext_set :=
  let v := fresh "z" in
   apply ext_eq_set; intro v; app_set_ext v; maprew.

Ltac app_ext_map :=
  apply ext_eq_map; intro v; app_set_ext v; maprew.

Ltac decide :=
  match goal with
    | |- context [ (match get ?A ?B with | Some a => ?t1 | None => ?t2 end)] => 
      Case_eq (get A B); intuition
    | |- context [ (if ?A then ?t1 else ?t2) ] => 
      Case_eq (A); intuition
  end. 

Ltac decide_ := decide; try discriminate.

Ltac map_or_set :=
match goal with
  | |- @eq kset _ _  => app_ext_set; repeat (decide_)
  | |- @eq kmap _ _  => app_ext_map; repeat (decide_)
end.
