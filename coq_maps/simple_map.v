Module Type Map.
  Parameter key : Type.
  Parameter kmap : Type.
  Parameter __set :
    forall (A : Type), key -> A -> kmap -> kmap.
  Parameter empty : kmap.
  Parameter combine : kmap -> kmap -> kmap.
  Parameter __get : 
    forall (A : Type), key -> kmap -> A.
End Map.

Module UnitMap : Map.
  Parameter key : Type.
  Definition kmap := unit.
  Definition __set (A : Type) (k : key)
    (v : A) (m : kmap) := m.
  Definition empty := tt.
  Definition combine (m1 m2 : kmap) := m1.
  Definition __get : 
    forall (A : Type), key -> kmap -> A.
  Admitted.

End UnitMap.

Export UnitMap.
