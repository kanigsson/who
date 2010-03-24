type ('a,'b) t = 'a * 'b

let compare cmpa cmpb (a1,b1) (a2,b2) =
  let c = cmpa a1 a2 in
  if c = 0 then cmpb b1 b2 else c

let equal eqa eqb (a1,b1) (a2,b2) = 
  eqa a1 a2 && eqb b1 b2

