Set Implicit Arguments.



Definition region : forall (u : Type) , Type. 
  Proof.
  Admitted.
   
Definition refty : forall (reg ty : Type) , Type. 
  Proof.
  Admitted.
   
Definition ref_get: forall (reg u : Type) ,  (region reg) -> (refty reg u) ->
  u.
  Proof.
  Admitted.
   
Require Import WhoTuples.
Require Import WhoArith.

Require Import WhoMap.
Require Import WhoArray.
Require Import WhoList.

Definition hashtbl : forall (a b : Type) , Type. 
  Proof.
  Admitted.
   
Definition Hashtbl_add: forall (a b r : Type) ,  (refty r (hashtbl a b)) ->
  a -> (b -> (region r) -> Prop) * (b -> (region r) -> (region r) -> unit ->
  Prop).
  Proof.
  Admitted.
   
Definition Hashtbl_create: forall (a b : Type) ,  (Z -> unit -> Prop) * (Z ->
  unit -> unit -> (hashtbl a b) -> Prop).
  Proof.
  Admitted.
   
Definition Hashtbl_mem: forall (a b : Type) ,  (hashtbl a b) -> a ->
  Prop.
  Proof.
  Admitted.
   
Definition Hashtbl_length: forall (a b : Type) ,  (hashtbl a b) ->
  Z.
  Proof.
  Admitted.
   
Hypothesis hashtbl_empty_lengh: forall (a b r : Type) ,
   forall (n:Z),
   ((@fst  (Z -> unit -> Prop) (Z -> unit -> unit -> (hashtbl a b) -> Prop))
    (@Hashtbl_create  a b) n tt)
   /\
   (forall (anon:hashtbl a b),
    ((@snd  (Z -> unit -> Prop) (Z -> unit -> unit -> (hashtbl a b) -> Prop))
     (@Hashtbl_create  a b) n tt tt anon)
    ->
    ((((@Hashtbl_length  a b) anon) = 0) /\
     (forall (x:a), ~ ((@Hashtbl_mem  a b) anon x)))). 
Hypothesis hashtbl_add: forall (a b r : Type) ,
   forall (x:a),
   forall (y:b),
   forall (hshtbl:refty r (hashtbl a b)),
   forall (s:region r),
   ((@fst  (b -> (region r) -> Prop) (b -> (region r) -> (region r) ->
    unit -> Prop)) ((@Hashtbl_add  a b r) hshtbl x) y s)
   /\
   (forall (s1:region r),
    ((@snd  (b -> (region r) -> Prop) (b -> (region r) -> (region r) ->
     unit -> Prop)) ((@Hashtbl_add  a b r) hshtbl x) y s s1 tt)
    -> ((@Hashtbl_mem  a b) ((@ref_get  r (hashtbl a b)) s1 hshtbl) x)). 
Hypothesis hashtbl_add_length: forall (a b r : Type) ,
   forall (x:a),
   forall (y:b),
   forall (hshtbl:refty r (hashtbl a b)),
   forall (s:region r),
   (~ ((@Hashtbl_mem  a b) ((@ref_get  r (hashtbl a b)) s hshtbl) x)) ->
   (((@fst  (b -> (region r) -> Prop) (b -> (region r) -> (region r) ->
     unit -> Prop)) ((@Hashtbl_add  a b r) hshtbl x) y s)
    /\
    (forall (s1:region r),
     ((@snd  (b -> (region r) -> Prop) (b -> (region r) -> (region r) ->
      unit -> Prop)) ((@Hashtbl_add  a b r) hshtbl x) y s s1 tt)
     ->
     (((@Hashtbl_length  a b) ((@ref_get  r (hashtbl a b)) s1 hshtbl)) =
      (((@Hashtbl_length  a b) ((@ref_get  r (hashtbl a b)) s hshtbl)) + 1)))). 
Hypothesis hashtbl_add_find: forall (a b r : Type) ,
   forall (x:a),
   forall (y:b),
   forall (hshtbl:refty r (hashtbl a b)),
   forall (s:region r),
   ((@fst  (b -> (region r) -> Prop) (b -> (region r) -> (region r) ->
    unit -> Prop)) ((@Hashtbl_add  a b r) hshtbl x) y s)
   /\
   (forall (s1:region r),
    ((@snd  (b -> (region r) -> Prop) (b -> (region r) -> (region r) ->
     unit -> Prop)) ((@Hashtbl_add  a b r) hshtbl x) y s s1 tt)
    ->
    (forall (s2:region r),
     ((@Hashtbl_mem  a b) ((@ref_get  r (hashtbl a b)) s2 hshtbl) x) /\
     (forall (anon:b), y = anon))). 
Definition List_append: forall (a : Type) ,  (list a) -> (list a) ->
  list a.
  Proof.
  Admitted.
   
Definition List_index: forall (a : Type) ,  Z -> (list a) ->
  a.
  Proof.
  Admitted.
   
Definition List_remove: forall (a : Type) ,  a -> (list a) ->
  list a.
  Proof.
  Admitted.
   
Definition List_length: forall (a : Type) ,  (list a) -> Z.
  Proof.
  Admitted.
   
Inductive List_mem ( a : Type) : a->
  (list a) -> Prop := | base_mem : forall (x:a),
                                   forall (l:list a),
                                   List_mem x ((@Cons  a) x l)
  | rec_mem : forall (x:a),
              forall (y:a),
              forall (l:list a),
              (List_mem x l) -> (List_mem x ((@Cons  a) y l)).
Inductive ind_list_rem ( a1 : Type) : a1-> (list a1)->
  (list a1) -> Prop := | base_success : forall (x:a1),
                                       forall (l:list a1),
                                       ind_list_rem x ((@Cons  a1) x l) l
  | base_failure : forall (x:a1),
                   forall (y:a1),
                   forall (l:list a1),
                   forall (l1:list a1),
                   (x <> y) ->
                   ((ind_list_rem x l l1) ->
                    (ind_list_rem x ((@Cons  a1) y l) ((@Cons  a1) y l1)))
  | base_nil : forall (x:a1), ind_list_rem x (@Nil  a1) (@Nil  a1).
Hypothesis list_remove_ind: forall (a : Type) ,
   forall (x:a),
   forall (l:list a),
   forall (l1:list a),
   (((@ind_list_rem  a) x l l1) -> (l1 = ((@List_remove  a) x l))) /\
   ((l1 = ((@List_remove  a) x l)) -> ((@ind_list_rem  a) x l l1)). 
Inductive ind_list_len ( a2 : Type) : (list a2)->
  Z -> Prop := | base : ind_list_len (@Nil  a2) 0
  | recur : forall (x:a2),
            forall (l:list a2),
            forall (n:Z),
            (ind_list_len l n) -> (ind_list_len ((@Cons  a2) x l) (n + 1)).
Hypothesis list_length_ind: forall (a : Type) ,
   forall (l:list a),
   forall (n:Z),
   (((@ind_list_len  a) l n) -> (n = ((@List_length  a) l))) /\
   ((n = ((@List_length  a) l)) -> ((@ind_list_len  a) l n)). 
Hypothesis remove_does_remove: forall (a : Type) ,
   forall (x:a),
   forall (l:list a), l = ((@List_remove  a) x ((@Cons  a) x l)). 
Section sec. 
   Variables a : Type.
  
  Variable x:  a. 
  Variable y:  a. 
  Variable l:  list a. 
  Hypothesis H: y <> x. 
  Lemma remove_does_not_rampage:
    ((@List_remove  a) y ((@Cons  a) x l)) =
    ((@Cons  a) x ((@List_remove  a) y l)). 
    Proof.
    remember (List_remove y l) as l1.
    assert (ind_list_rem y (Cons x l) (Cons x l1)).
      assert (ind_list_rem y l l1).
        remember list_remove_ind as H1.
        apply (H1 a y l l1).
        apply Heql1.

        apply (base_failure H H0).

        pose proof (list_remove_ind y (Cons x l) (Cons x l1)) as H42.
        destruct H42.
        symmetry.
        apply (H1 H0).
     Qed.

     End sec.
