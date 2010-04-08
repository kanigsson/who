Notation "'mk_2tuple'" := pair (only parsing).
Notation "'mk_3tuple'" := (fun a b c => (a,b,c)) (only parsing).
Notation "'mk_4tuple'" := (fun a b c d => (a,b,c,d)) (only parsing).
Notation "'mk_5tuple'" := (fun a b c d e => (a,b,c,d,e)) (only parsing).
Notation "'mk_6tuple'" := (fun a b c d e f => (a,b,c,d,e,f)) (only parsing).
Notation "'mk_7tuple'" := (fun a b c d e f g => (a,b,c,d,e,f,g)) (only parsing).

Notation "'get_2_1_tuple'" :=
  (fun p => let (a,b) := p in a) (only parsing).
Notation "'get_2_2_tuple'" :=
  (fun p => let (a,b) := p in b) (only parsing).
Notation "'get_3_1_tuple'" :=
  (fun p => let (a,b,c) := p in a) (only parsing).
Notation "'get_3_2_tuple'" :=
  (fun p => let (a,b,c) := p in b) (only parsing).
Notation "'get_3_3_tuple'" :=
  (fun p => let (a,b,c) := p in c) (only parsing).
Notation "'get_4_1_tuple'" :=
  (fun p => let (a,b,c,d) := p in a) (only parsing).
Notation "'get_4_2_tuple'" :=
  (fun p => let (a,b,c,d) := p in b) (only parsing).
Notation "'get_4_3_tuple'" :=
  (fun p => let (a,b,c,d) := p in c) (only parsing).
Notation "'get_4_4_tuple'" :=
  (fun p => let (a,b,c,d) := p in d) (only parsing).
Notation "'get_5_1_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in a) (only parsing).
Notation "'get_5_2_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in b) (only parsing).
Notation "'get_5_3_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in c) (only parsing).
Notation "'get_5_4_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in d) (only parsing).
Notation "'get_5_5_tuple'" :=
  (fun p => let (a,b,c,d,e) := p in e) (only parsing).