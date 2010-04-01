type t = Effect.t * Effect.t

let equal (a1,b1) (a2,b2) = Effect.equal a1 a2 && Effect.equal b1 b2

let empty = Effect.empty, Effect.empty

let is_empty (e1,e2) = Effect.is_empty e1 && Effect.is_empty e2

let union (l1,l2) (r1,r2) = Effect.union l1 r1, Effect.union l2 r2
let union3 a b c = union a (union b c)

let rremove (e1,e2) rl = Effect.rremove e1 rl, Effect.rremove e2 rl

let overapprox (e1,e2) = Effect.union e1 e2

let kernel (e1,e2) = Effect.inter e1 e2

module Convert = struct
  let t env (e1,e2) = Effect.Convert.t env e1, Effect.Convert.t env e2
end

module Print = struct
  open PrintTree

  let emp = Name.Env.empty Name.M.empty
  let rw fmt e = Print.rw fmt (Convert.t emp e)
end

let print = Print.rw

