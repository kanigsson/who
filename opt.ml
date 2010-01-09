let get def x = 
  match x with
  | None -> def
  | Some x -> x

let get_map def f x =
  match x with
  | None -> def
  | Some x -> f x

let map f x = 
  match x with
  | None -> None
  | Some x -> Some (f x)
