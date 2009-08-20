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

"
