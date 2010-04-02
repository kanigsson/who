type t =
  (* We incode the invariant write \subseteq read by saying that [read] contains
   * only the effects that are not already contained in [write]. *)
  {
    read : Effect.t ;
    write : Effect.t
  }

let mk ~read ~write =
  { write = write; read = Effect.diff read write }

let reads a = Effect.union a.read a.write
let writes a = a.write
let reads_only a = a.read

let read_write a = reads a, writes a

let map f e =
  { read = f e.read ; write = f e.write }

let empty = { read = Effect.empty; write = Effect.empty }

let equal e1 e2 =
  Effect.equal e1.read e2.read && Effect.equal e1.write e2.write

let is_empty rw =
  Effect.is_empty rw.read && Effect.is_empty rw.write

let union e1 e2 =
  mk ~read:(Effect.union e1.read e2.read)
    ~write:(Effect.union e1.write e2.write)

let union3 a b c = union a (union b c)

let rremove e rl = map (fun e -> Effect.rremove e rl) e
let overapprox e = reads e

let kernel e = e.write

module Convert = struct
  let t env e =
    Effect.Convert.t env e.read, Effect.Convert.t env e.write
end

module Print = struct
  open PrintTree

  let emp = Name.Env.empty Name.M.empty
  let rw fmt e = Print.rw fmt (Convert.t emp e)
end

let print = Print.rw

