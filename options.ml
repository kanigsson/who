let filename = ref ""
let store_fn x = filename := x
let abort cin = close_in cin ; exit 1
let parse_only = ref false
let infer_only = ref false
let constr_only = ref false
let anf_only = ref false
let wp_only = ref false
let simplify_only = ref false
let sectionize_only = ref false
let prelude = ref false
let outfile = ref ""
let check_coq = ref false
let backend : [ `Coq | `Pangoline ] ref = ref `Coq
let suffix = ref ".v"

let opt_spec = 
  Arg.align
  [ 
    "-parse-only", Arg.Set parse_only, " parse file and exit";
    "-infer-only", Arg.Set infer_only, " do type inference and exit";
    "-constr-only", Arg.Set constr_only, " construct fully typed term and exit";
    "-anf-only", Arg.Set anf_only, " construct anf normal form and exit";
    "-wp-only", Arg.Set wp_only, " construct wp formula and exit";
    "-simplify-only", Arg.Set simplify_only, " construct simplified wp formula and exit";
    "-sectionize-only", Arg.Set sectionize_only, " construct sectionized wp formula and exit";
    "-o", Arg.Set_string outfile, 
            "<arg> use <arg> instead of default filename for output";
    "-pangoline", Arg.Unit (fun () -> backend := `Pangoline; suffix := ".pge" ), 
            " set output format to pangoline";
    "-check-coq", Arg.Set check_coq, " check produced coq file using coqc";
  ]

let () = Arg.parse opt_spec store_fn "Usage: who <options> <file>"

let update () = 
  if !filename = "" then (Myformat.eprintf "No filename given"; exit(1));
  let base = Filename.chop_extension !filename in
  if !outfile = "" then outfile := Myformat.sprintf "%s_who%s" base !suffix
