module SM = Misc.StringMap

module SS = Misc.SS

open Ty
let typing_env = 
  let a = "a" and b = "b" and r = "r" and ev = "e" in
  let va = var a and vb = var b and re = Effect.rsingleton r 
  and ef = Effect.esingleton ev in
  let l = 
    [
      "=", (([a],[],[]), parr va (parr va prop));
      "<>", (([a],[],[]), parr va (parr va prop));
      "==", (([a],[],[]), parr va (parr va bool));
      "!=", (([a],[],[]), parr va (parr va bool));
      "!", (([a],[r],[]), arrow (ref_ r va) va re);
      "!!", (([a],[r],[ev]), parr (ref_ r va) (parr (map ef) ( va)));
      ":=", (([a],[r],[]), parr (ref_ r va) (arrow va unit re));
      "snd", (([a;b],[],[]), parr (tuple va vb) vb);
      "fst", (([a;b],[],[]), parr (tuple va vb) va);
      "+", (([],[],[]), parr int (parr int int));
    ] in
  List.fold_left (fun acc (x,s) -> SM.add x s acc) SM.empty l
