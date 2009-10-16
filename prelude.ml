let prelude = "
section basiclogic
  coq predefined
  logic /\\ : prop -> prop -> prop
  logic \\/ : prop -> prop -> prop
  logic -> : prop -> prop -> prop
  logic ~ : prop -> prop
  logic = ['a||] : 'a -> 'a -> prop
  logic <> ['a||] : 'a -> 'a -> prop
  logic fst ['a 'b||] : 'a * 'b -> 'a
  logic snd ['a 'b||] : 'a * 'b -> 'b
  logic , ['a 'b||] : 'a -> 'b -> 'a * 'b
end

section arith
  coq \"WhoArith\"
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
  logic max : int -> int -> int
  logic min : int -> int -> int
  logic mod : int -> int -> int
end


logic == ['a||] : 'a -> 'a -> bool
logic != ['a||] : 'a -> 'a -> bool

section Whoref
  coq \"WhoMap\"
  logic !! ['a|r|e] : ref(r,'a) -> <|e> -> 'a
  parameter ! ['a|r|] (x : ref(r,'a)) : 'a, {r|} =
    {}
    {r : !!x = r /\\ !!x|old = !!x}

  parameter := ['a|r|] (x : ref(r,'a)) (v : 'a) : unit, {r|} =
    {}
    { !!x = v}

  parameter ref ['a|r|] (v : 'a) : ref(r,'a), {r||r} =
    {}
    { x : !!x = v }

  logic combine [||e1 e2] : <|e1> -> <|e2> -> <|e1 e2>
  logic restrict [||e1 e2] : <|e1> -> <|e2>
  logic empty : <|>

  type kmap
  type key
  logic kcombine [||e1 e2] : kmap -> kmap -> kmap
  logic krestrict [||e1 e2] : kmap -> kmap
  logic kset ['a||] : key -> 'a -> kmap -> kmap
  logic kget ['a|r|] : ref(r,'a) -> kmap -> 'a
  logic kempty : kmap 
  let pre ['a 'b||] (x : 'a * 'b) = fst x
  let post ['a 'b||] (x : 'a * 'b) = snd x
end

parameter forto [||e] (inv : int -> <|e> -> prop) (start end_ : int) 
  (f : int ->{|e} unit) : unit, {|e} =
    { inv start cur /\\
          forall (i : int). start <= i /\\ i <= end_ ->
          forall (m : <|e>) . inv i m -> pre f i m /\\
          forall (n : <|e>). post f i m n () -> inv (i+1) n
    }
    { inv (max start (end_ + 1)) cur} 


parameter fordownto [||e] (inv :  int -> <|e> -> prop) (start end_ : int) 
  (f : int ->{|e} unit) : unit, {|e} =
    { inv start cur /\\
          forall (i : int). start <= i /\\ i <= end_ ->
          forall (m : <|e>) . inv i m -> pre f i m /\\
          forall (n : <|e>). post f i m n () -> inv (i-1) n
    }
    { inv (min start (end_ - 1)) cur }

section Array
  coq \"WhoArray\"
  type array ['a||]

  logic get ['a||] : int -> 'a array -> 'a
  logic set ['a||]: int -> 'a -> 'a array -> 'a array 
  logic len ['a||] :  'a array -> int
  (* logic create ['a||] :  int -> 'a array *)

  axiom update_length ['a||] : 
    forall (t : 'a array) (i : int) (z : 'a).
      len t = len (set i z t)

  axiom get_set_eq ['a||] : 
    forall (t : 'a array) (i : int) (z : 'a).
      i < len t -> get i (set i z t) = z

  axiom get_set_neq ['a||] : 
    forall (t : 'a array ) (i : int) (j : int) (z : 'a).
      i < len t -> j < len t -> i <> j -> get i (set j z t) = get i t

  axiom length_nonnegative ['a||] : 
    forall (t : array ['a||]).  0 <= len t

  (* axiom length_create ['a||] : 
    forall (l : int). 0 <= l -> length ((create l : 'a array)) = l *)
end

section List
  coq \"WhoList\"
  type list ['a||]

  logic nil ['a||] : 'a list
  logic cons ['a||] : 'a -> 'a list -> 'a list

  logic is_nil ['a||] : 'a list -> bool
  logic l_in ['a||] : 'a -> 'a list -> prop
end

"

