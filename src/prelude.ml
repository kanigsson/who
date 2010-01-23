let prelude = "
section basiclogic
  coq predefined
  pangoline predefined
  logic /\\ : prop -> prop -> prop
  logic \\/ : prop -> prop -> prop
  logic -> : prop -> prop -> prop
  logic ~ : prop -> prop
  logic = ['a||] : 'a -> 'a -> prop
  logic , ['a 'b||] : 'a -> 'b -> 'a * 'b
end

section pairs
  coq predefined
  pangoline takeover
  logic fst ['a 'b||] : 'a * 'b -> 'a
  logic snd ['a 'b||] : 'a * 'b -> 'b
end

section boolean
  coq predefined
  pangoline takeover
  type bool
  logic true : bool
  logic false : bool
end

section arith
  coq \"WhoArith\"
  pangoline takeover
  logic + : int -> int -> int
  logic - : int -> int -> int
  logic * : int -> int -> int
  logic < : int -> int -> prop
  logic <= : int -> int -> prop
  logic > : int -> int -> prop
  logic >= : int -> int -> prop
  logic << : int -> int -> bool
  logic <<= : int -> int -> bool
  logic >> : int -> int -> bool
  logic >>= : int -> int -> bool
  logic <> ['a||] : 'a -> 'a -> prop
  logic int_max : int -> int -> int
  logic int_min : int -> int -> int
  logic mod_int : int -> int -> int
  logic band : bool -> bool -> bool
  logic bor : bool -> bool -> bool

  axiom int_max_is_ge :  
    forall (x y :int).
      int_max x y >= x /\\ int_max x y >= y

  axiom int_max_is_some :  
    forall (x y : int).
      int_max x y = x \\/ int_max x y = y 

  axiom int_min_is_le :  
    forall (x y : int).
      int_min x y <= x /\\ int_min x y <= y

  axiom int_min_is_some :  
    forall (x y : int).
      int_min x y = x \\/ int_min x y = y 

end


logic == ['a||] : 'a -> 'a -> bool
logic != ['a||] : 'a -> 'a -> bool

section Whoref
  coq \"WhoMap\"
  pangoline predefined

  logic !! ['a|r|'e] : ref(r,'a) -> <r 'e > -> 'a
  parameter ! ['a|r|] (x : ref(r,'a)) : 'a, {r} =
    {}
    {r : !!x = r /\\ !!x|old = !!x}

  parameter := ['a|r|] (x : ref(r,'a)) (v : 'a) : unit, {r} =
    {}
    { !!x = v}

  parameter ref ['a|r|] (v : 'a) : ref(r,'a), {r} = allocates r
    {}
    { x : !!x = v }

  logic combine [||'e1 'e2 'e3] : <'e1 'e2> -> <'e2 'e3> -> <'e1 'e2 'e3>
  logic restrict [||'e1 'e2] : <'e1 'e2> -> <'e2>
  logic empty : < >

  let pre ['a 'b||] (x : 'a * 'b) = fst x
  let post ['a 'b||] (x : 'a * 'b) = snd x
end

parameter forto [||'e] (inv : int -> <'e> -> prop) (start end_ : int) 
  (f : int ->{'e} unit) : unit, {'e} =
    { inv start cur /\\
          forall (i : int). start <= i /\\ i <= end_ ->
          forall (m : <'e>) . inv i m -> pre f i m /\\
          forall (n : <'e>). post f i m n () -> inv (i+1) n
    }
    { inv (int_max start (end_ + 1)) cur} 


parameter fordownto [||'e] (inv :  int -> <'e> -> prop) (start end_ : int) 
  (f : int ->{'e} unit) : unit, {'e} =
    { inv start cur /\\
          forall (i : int). end_ <= i /\\ i <= start ->
          forall (m : <'e>) . inv i m -> pre f i m /\\
          forall (n : <'e>). post f i m n () -> inv (i-1) n
    }
    { inv (int_min start (end_ - 1)) cur }

section Array
  coq \"WhoArray\"
  pangoline takeover
  type array ['a||]

  logic ar_empty ['a||] : 'a array
  logic get ['a||] : int -> 'a array -> 'a
  logic set ['a||]: int -> 'a -> 'a array -> 'a array 
  logic len ['a||] :  'a array -> int
  logic create ['a||] :  int -> 'a -> 'a array

  axiom update_length ['a||] : 
    forall (t : 'a array) (i : int) (z : 'a).
      len t = len (set i z t)

  axiom get_set_eq ['a||] : 
    forall (t : 'a array) (i : int) (z : 'a).
      i < len t -> get i (set i z t) = z

  axiom length_empty ['a||] : len (ar_empty : 'a array) = 0

  axiom get_set_neq ['a||] : 
    forall (t : 'a array ) (i : int) (j : int) (z : 'a).
      i < len t -> j < len t -> i <> j -> get i (set j z t) = get i t

  axiom length_nonnegative ['a||] : 
    forall (t : array ['a||]).  0 <= len t

  axiom length_create ['a||] : 
    forall (l : int) (v : 'a). 0 <= l -> len (create l v) = l

  axiom length_access ['a||] :
    forall (i l : int) (v : 'a). 0 <= i -> i <= l -> get i (create l v) = v
end

section List
  coq \"WhoList\"
  pangoline takeover
  type list ['a||]

  logic nil ['a||] : 'a list
  logic cons ['a||] : 'a -> 'a list -> 'a list

  logic is_nil ['a||] : 'a list -> bool
  logic l_in ['a||] : 'a -> 'a list -> prop
end

"

