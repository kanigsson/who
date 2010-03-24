let combine acc n = n * 65599 + acc
let combine2 acc n1 n2 = combine acc (combine n1 n2)
let combine3 acc n1 n2 n3 = combine acc (combine n1 (combine n2 n3))
let combine_list f = List.fold_left (fun acc x -> combine acc (f x))
let combine_option h = function
  | None -> 0
  | Some s -> (h s) + 1
let combine_pair h1 h2 (a1,a2) = combine (h1 a1) (h2 a2)
