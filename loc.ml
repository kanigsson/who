type loc = {st: int * int; en: int * int}
type 'a t = { info:loc ; c : 'a }
let dummy = {st = (0,0); en = (0,0) }

let with_dummy v = { c = v; info = dummy }

let mk i v = { c = v; info =i }

let with_loc f v = { c = f v.c; info = v.info }
