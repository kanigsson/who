let verbose = ref false
let dontclean = ref false
type provers = [ `Z3 | `Yices ]
let prover : provers ref = ref `Z3
let file_list = ref []
let dp_opts = ref ""
let append_file s = file_list := s :: !file_list

let args = 
  Arg.align
  [ 
    "-v", Arg.Set verbose, " be more verbose";
    "--dpopts", Arg.Set_string dp_opts, " pass these options to why-dp";
    "--dont-clean", Arg.Set dontclean, " don't remove generated files";
    "--verbose", Arg.Set verbose, " be more verbose";
  ]

let _ = 
  Arg.parse args append_file "usage: whyz3 <options> file1 file2 ..."


let ksprintf k s =
  ignore(Format.flush_str_formatter ());
  Format.kfprintf (fun _ -> k (Format.flush_str_formatter ())) 
    Format.str_formatter s

let sprintf s = ksprintf (fun x -> x) s

let do_ s = 
  if !verbose then Format.eprintf "%s@." s;
  ignore (Sys.command s)
let do_with_fn cmd fn = do_ (sprintf "%s %s" cmd fn)  

let rm = do_with_fn "rm -f" 
let why s = 
  let opt = 
    match !prover with
    | `Z3 -> "--z3"
    | `Yices -> "--yices" in
  do_with_fn (sprintf "why %s" opt) s

let why_output =
  let regexp = Str.regexp "\\(\\.why\\|\\.mlw\\)$" in
  fun s -> 
    let ext = 
      match !prover with
      | `Z3 -> "z3"
      | `Yices -> "yices"
    in
    let r = Str.replace_first regexp (sprintf "_why.%s.smt" ext) s in
    if r = s then failwith "could not replace suffix"
    else r

let file_args fmt a = List.iter (Format.fprintf fmt "%s ") a
let whydp a = do_ (sprintf "why-dp %s %a" !dp_opts file_args a)

let _ = 
  let files = List.rev !file_list in
  let z3files = List.map (fun x -> why x; why_output x) files in
  whydp z3files;
  if !dontclean then ()
  else List.iter rm z3files




