let prelude = "
logic /\\ : prop -> prop -> prop
logic -> : prop -> prop -> prop
logic ~ : prop -> prop
logic = ['a||] : 'a -> 'a -> prop
logic <> ['a||] : 'a -> 'a -> prop
logic fst ['a 'b||] : 'a * 'b -> 'a
logic snd ['a 'b||] : 'a * 'b -> 'b
logic , ['a 'b||] : 'a -> 'b -> 'a * 'b

logic == ['a||] : 'a -> 'a -> bool
logic != ['a||] : 'a -> 'a -> bool
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

logic + : int -> int -> int
logic - : int -> int -> int
logic * : int -> int -> int
logic < : int -> int -> prop
logic <= : int -> int -> prop
logic > : int -> int -> prop
logic >= : int -> int -> prop
logic max : int -> int -> int
logic min : int -> int -> int

let pre ['a 'b||]  (x : 'a * 'b) = fst x
let post ['a 'b||] (x : 'a * 'b) = snd x

logic combine [||e1 e2] : <|e1> -> <|e2> -> <|e1 e2>
logic restrict [||e1 e2] : <|e1> -> <|e2>

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

type array ['a||]

logic get ['a||] : int -> 'a array -> 'a
logic set ['a||]: int -> 'a -> 'a array -> 'a array 
logic length ['a||] :  'a array -> int
logic create ['a||] :  int -> 'a array

axiom update_length ['a||] : 
  forall (t : 'a array) (i : int) (z : 'a).
    length t = length (set i z t)

axiom get_set_eq ['a||] : 
  forall (t : 'a array) (i : int) (z : 'a).
    i < length t -> get i (set i z t) = z

axiom get_set_neq ['a||] : 
  forall (t : 'a array ) (i : int) (j : int) (z : 'a).
    i < length t -> j < length t -> i <> j -> get i (set j z t) = get i t

axiom length_nonnegative ['a||] : 
  forall (t : array ['a||]).  0 <= length t

axiom length_create ['a||] : 
  forall (l : int). 0 <= l -> length ((create l : 'a array)) = l

"

