module SM = Misc.StringMap

(*
module Infer = struct
  open Unify
  let infer_env = 
    let nv = new_ty () in
    SM.add "beq_z" (0, arrow nv (arrow nv (const Const.TBool))) SM.empty
end

let infer_env = Infer.infer_env
*)

module SS = Misc.SS
open Ty
let typing_env = 
  let a = "a" in
  let b = "b" in
  let va = var a in
  let vb = var b in
  let r = "r" in
  let se = SS.empty in
  let re = SS.add r se, se in
  let l = 
    [
      "beq_z", (([a],[],[]), parr va (parr va bool));
      "!", (([a],[r],[]), arrow (ref_ r va) va re);
      ":=", (([a],[r],[]), parr (ref_ r va) (arrow va unit re));
      "snd", (([a;b],[],[]), parr (tuple va vb) vb);
      "fst", (([a;b],[],[]), parr (tuple va vb) va);
    ] in
  List.fold_left (fun acc (x,s) -> SM.add x s acc) SM.empty l
