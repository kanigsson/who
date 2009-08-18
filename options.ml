let filename = ref ""
let store_fn x = filename := x
let abort cin = close_in cin ; exit 1
let parse_only = ref false
let infer_only = ref false
let constr_only = ref false
let anf_only = ref false

let opt_spec = 
  Arg.align
  [ 
    "-parse-only", Arg.Set parse_only, " parse file and exit";
    "-infer-only", Arg.Set infer_only, " do type inference and exit";
    "-constr-only", Arg.Set constr_only, "construct fully typed term and exit";
    "-anf-only", Arg.Set anf_only, "construct anf normal form and exit";
  ]

let () = 
  Arg.parse opt_spec store_fn "Usage: who <options> <file>"

let update () = 
  if !filename = "" then (Format.eprintf "No filename given"; exit(1))
