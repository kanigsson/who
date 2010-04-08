Notation "'mk_2tuple'" := pair.
Notation "'mk_3tuple'" := (fun a b c => (a,b,c)).
Notation "'mk_4tuple'" := (fun a b c d => (a,b,c,d)).
Notation "'mk_5tuple'" := (fun a b c d e => (a,b,c,d,e)).
Notation "'mk_6tuple'" := (fun a b c d e f => (a,b,c,d,e,f)).
Notation "'mk_7tuple'" := (fun a b c d e f g => (a,b,c,d,e,f,g)).

Notation "'get_2_1_tuple'" :=
  (fun p => let (a,b) := p in a).
Notation "'get_2_2_tuple'" :=
  (fun p => let (a,b) := p in b).
Notation "'get_3_1_tuple'" :=
  (fun p => let (a,b,c) := p in a).
Notation "'get_3_2_tuple'" :=
  (fun p => let (a,b,c) := p in b).
Notation "'get_3_3_tuple'" :=
  (fun p => let (a,b,c) := p in c).
Notation "'get_4_1_tuple'" :=
  (fun p => let (a,b,c,d) := p in a).
Notation "'get_4_2_tuple'" :=
  (fun p => let (a,b,c,d) := p in b).
Notation "'get_4_3_tuple'" :=
  (fun p => let (a,b,c,d) := p in c).
Notation "'get_4_4_tuple'" :=
  (fun p => let (a,b,c,d) := p in d).
Notation "'get_5_1_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in a).
Notation "'get_5_2_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in b).
Notation "'get_5_3_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in c).
Notation "'get_5_4_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in d).
Notation "'get_5_5_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in e).


