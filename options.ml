let filename = ref None
let store_fn x = filename := Some x
let abort cin = close_in cin ; exit 1
let parse_only = ref false
let infer_only = ref false
let constr_only = ref false
let no_prelude = ref false
let outfile = ref ""
let check_coq = ref false
let input_annot = ref false
let backend : [ `Coq | `Pangoline ] ref = ref `Coq
let suffix = ref ".v"

let transforms = 
  ref (List.rev  [ Anf.theory ; Wp.theory ])

let append_trans x () = transforms := x :: !transforms

let clear () = transforms := []

let opt_spec = 
  Arg.align
  [ 
    "-input-annot", Arg.Set input_annot, "take fully type annotated input file";
    "-parse-only", Arg.Set parse_only, " parse file and exit";
    "-infer-only", Arg.Set infer_only, " do type inference and exit";
    "-clear", Arg.Unit clear, " clear the list of transformations";
    "-anf", Arg.Unit (append_trans Anf.theory),
      " apply anf normal form transformation";
    "-wp", Arg.Unit (append_trans Wp.theory),
      " apply weakest precondition calculus";
    "-o", Arg.Set_string outfile, 
            "<arg> use <arg> instead of default filename for output";
    "-pangoline", Arg.Unit (fun () -> backend := `Pangoline; suffix := ".pge" ), 
            " set output format to pangoline";
    "-check-coq", Arg.Set check_coq, " check produced coq file using coqc";
    "-no-prelude", Arg.Set no_prelude, " do not add a prelude to the file";
  ]

let () = Arg.parse opt_spec store_fn "Usage: who <options> <file>"

let update () = 
  let base = 
    match !filename with
    | None -> "base"
    | Some s -> Filename.chop_extension s in
  if !outfile = "" then outfile := Myformat.sprintf "%s_who%s" base !suffix
