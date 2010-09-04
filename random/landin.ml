let backpatch =
  let id x = x in
  fun f ->
    let x = ref id in
    x:= (fun z -> f !x z);
    !x

let n = 10

let _ =
  let x = backpatch (fun r n -> if n = 0 then 1 else n * r (n-1)) 10 in
  print_int x;
  print_newline ()

