Add LoadPath "../../coq_files/".
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
Inductive ind_list_rem ( a : Type) : a-> (list a)->
  (list a) -> Prop := | base_success : forall (x:a),
                                       forall (l:list a),
                                       ind_list_rem x ((@Cons  a) x l) l
  | base_failure : forall (x:a),
                   forall (y:a),
                   forall (l:list a),
                   forall (l1:list a),
                   (x <> y) ->
                   ((ind_list_rem x l l1) ->
                    (ind_list_rem x ((@Cons  a) y l) ((@Cons  a) y l1)))
  | base_nil : forall (x:a), ind_list_rem x (@Nil  a) (@Nil  a).
Hypothesis list_remove_ind: forall (a : Type) ,
   forall (x:a),
   forall (l:list a),
   forall (l1:list a),
   (((@ind_list_rem  a) x l l1) -> (l1 = ((@List_remove  a) x l))) /\
   ((l1 = ((@List_remove  a) x l)) -> ((@ind_list_rem  a) x l l1)). 
Inductive ind_list_len ( a : Type) : (list a)->
  Z -> Prop := | base : ind_list_len (@Nil  a) 0
  | recur : forall (x:a),
            forall (l:list a),
            forall (n:Z),
            (ind_list_len l n) -> (ind_list_len ((@Cons  a) x l) (n + 1)).
Hypothesis list_length_ind: forall (a : Type) ,
   forall (l:list a),
   forall (n:Z),
   (((@ind_list_len  a) l n) -> (n = ((@List_length  a) l))) /\
   ((n = ((@List_length  a) l)) -> ((@ind_list_len  a) l n)). 
Hypothesis remove_does_remove: forall (a : Type) ,
   forall (x:a),
   forall (l:list a), l = ((@List_remove  a) x ((@Cons  a) x l)). 
Hypothesis remove_does_not_rampage: forall (a : Type) ,
   forall (x:a),
   forall (y:a),
   forall (l:list a),
   (y <> x) ->
   (((@List_remove  a) y ((@Cons  a) x l)) =
    ((@Cons  a) x ((@List_remove  a) y l))). 
Hypothesis remove_empty: forall (a : Type) ,
   forall (x:a), (@Nil  a) = ((@List_remove  a) x (@Nil  a)). 
Hypothesis append_does_append: forall (a : Type) ,
   forall (l:list a),
   forall (l1:list a),
   forall (x:a),
   (((@List_mem  a) x l) -> ((@List_mem  a) x ((@List_append  a) l l1))) /\
   (((@List_mem  a) x l1) -> ((@List_mem  a) x ((@List_append  a) l l1))). 
Hypothesis append_match: forall (a : Type) ,
   forall (l:list a),
   forall (l1:list a),
   match l with Cons x (Nil) =>
                 ((@List_append  a) l l1) = ((@Cons  a) x l1)  | Nil =>
                 l1 = ((@List_append  a) l l1)  | Cons x l2 =>
                 ((@List_append  a) l l1) =
                 ((@Cons  a) x ((@List_append  a) l2 l1))  end . 
Hypothesis list_length_nil: forall (a : Type) ,
   ((@List_length  a) (@Nil  a)) = 0. 
Hypothesis list_length_pos: forall (a : Type) ,
   forall (l:list a), ((@List_length  a) l) >= 0. 
Hypothesis list_length_map: forall (a b e : Type) ,
   forall (l:list a),
   forall (f_pre:a -> e -> Prop),
   forall (f_post:a -> e -> e -> b -> Prop),
   forall (ia:e -> (list a) -> Prop),
   forall (ib:(list b) -> Prop),
   forall (s:e),
   (((ia s l) /\ (ib (@Nil  b))) /\
    (forall (x:a),
     forall (l1:list a),
     forall (k:list b),
     forall (s1:e),
     (ia s1 ((@Cons  a) x l1)) ->
     ((ib k) ->
      ((f_pre x s1) /\
       (forall (s2:e),
        forall (anon:b),
        (f_post x s1 s2 anon) -> ((ia s2 l1) /\ (ib ((@Cons  b) anon k))))))))
   /\
   (forall (s1:e),
    forall (anon:list b),
    (ia s1 (@Nil  a)) ->
    ((ib anon) -> (((@List_length  a) l) = ((@List_length  b) anon)))). 
Hypothesis list_index_map: forall (a b e : Type) ,
   forall (x:a),
   forall (l:list a),
   forall (i:Z),
   forall (f_pre:a -> e -> Prop),
   forall (f_post:a -> e -> e -> b -> Prop),
   forall (ia:e -> (list a) -> Prop),
   forall (ib:(list b) -> Prop),
   (i >= 0) ->
   ((i < ((@List_length  a) l)) ->
    (forall (s:e),
     (((ia s l) /\ (ib (@Nil  b))) /\
      (forall (x1:a),
       forall (l1:list a),
       forall (k:list b),
       forall (s1:e),
       (ia s1 ((@Cons  a) x1 l1)) ->
       ((ib k) ->
        ((f_pre x1 s1) /\
         (forall (s2:e),
          forall (anon:b),
          (f_post x1 s1 s2 anon) -> ((ia s2 l1) /\ (ib ((@Cons  b) anon k))))))))
     /\
     (forall (s1:e),
      forall (anon:list b),
      (ia s1 (@Nil  a)) ->
      ((ib anon) ->
       (forall (s2:e),
        (f_pre ((@List_index  a) i l) s2) /\
        (forall (s3:e),
         forall (anon1:b),
         (f_post ((@List_index  a) i l) s2 s3 anon1) ->
         (anon1 = ((@List_index  b) i anon)))))))). 
Hypothesis list_cons_mem: forall (a : Type) ,
   forall (x:a), forall (l:list a), (@List_mem  a) x ((@Cons  a) x l). 
Hypothesis list_cons_mem_tail: forall (a : Type) ,
   forall (x:a),
   forall (l:list a),
   forall (y:a), ((@List_mem  a) y l) -> ((@List_mem  a) y ((@Cons  a) x l)). 
Hypothesis list_cons_length_tail: forall (a : Type) ,
   forall (x:a),
   forall (l:list a),
   ((@List_length  a) ((@Cons  a) x l)) = (((@List_length  a) l) + 1). 
Hypothesis list_index: forall (a : Type) ,
   forall (i:Z),
   forall (l:list a),
   match l with Cons x l1 =>  (i = 0) -> (x = ((@List_index  a) i l))|Nil => True end . 
Hypothesis list_index_rec: forall (a : Type) ,
   forall (i:Z),
   forall (l:list a),
   match l with Cons x l1 =>
                 (i > 0) ->
                 ((i < ((@List_length  a) l)) ->
                  (((@List_index  a) i l) = ((@List_index  a) (i - 1) l1))) |Nil => True end . 
Hypothesis list_mem_inverse: forall (a : Type) ,
   forall (x:a),
   forall (x1:a),
   forall (l:list a),
   forall (l1:list a),
   match l with Cons x2 l2 =>
                 (~ ((@List_mem  a) x l)) ->
                 ((x2 <> x) /\ (~ ((@List_mem  a) x l2))) |Nil => True end . 
Section sec. 
   Variables a : Type.
  
  Variable x:  a. 
  Variable l:  list a. 
  Hypothesis H: ~ ((@List_mem  a) x l). 
  Lemma g: l = ((@List_remove  a) x l). 
    Proof.
    induction l.
      apply remove_empty.
      
      intros.
      assert (x <> a0).
        contradict H.
        rewrite H.
        apply (base_mem a0).

      assert (~ (List_mem x l0)).
        contradict H.
        apply rec_mem.
        assumption.

      pose proof (IHl0 H1).
      pose proof (list_remove_ind x (Cons a0 l0) (Cons a0 l0)).
      destruct H3.
      apply H3. clear H3 H4.
      
      pose proof (list_remove_ind x l0 l0).
      destruct H3.
      pose proof (H4 H2). clear H3 H4.
      
      apply (base_failure H0 H5).
      Qed.
        
End sec.
