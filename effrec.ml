open Ast
open Ast.Recon

type t = Name.t Name.M.t * Name.t Name.M.t

let e_combine (r1,e1) (r2,e2) = 
  Name.M.fold Name.M.add r2 r1,
  Name.M.fold Name.M.add e2 e1

let e_restrict d (r,e) = 
  Name.M.fold (fun k v acc -> 
    if NEffect.rmem d k then Name.M.add k v acc else acc) r Name.M.empty,
  Name.M.fold (fun k v acc -> 
    if NEffect.emem d k then Name.M.add k v acc else acc) e Name.M.empty

let rec from_form d x = 
(*   Myformat.printf "finding effrec for %a@." print' x; *)
  match destruct_combine' x with
  | Some (m1,_,m2,_) -> e_combine (from_form_t m1.t m1.v) (from_form_t m2.t m2.v)
  | None -> 
      match destruct_restrict' x with
      | Some (m,_,e2) -> e_restrict e2 (from_form_t m.t m.v)
      | None ->
          match x with
          | Var (s,_) -> 
              NEffect.rfold (fun k acc -> Name.M.add k s acc) Name.M.empty d,
              NEffect.efold (fun k acc -> Name.M.add k s acc) Name.M.empty d 
          | _ -> 
              Myformat.printf "strange term: %a@." print' x;
              assert false
and from_form_t t x = from_form (Ty.domain t) x

let rfold f (r,_) acc = Name.M.fold f r acc
let efold f (_,e) acc = Name.M.fold f e acc
