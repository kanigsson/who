let parse ?(prelude=false) buf close fn = 
  if prelude then Options.prelude := true else Options.prelude := false;
  let abort () = close (); exit 1 in
  Lexer.reset buf;
  try 
    let prog = Parser.main Lexer.token buf in
    prog
  with 
  | Parser.Error -> 
      Error.print_pos_error fn buf "Parse error"; abort ()
  | Lexer.Error msg -> 
        Error.print_pos_error fn buf 
          (Myformat.sprintf "Unexpected character: %s" msg);
        abort ()

let maybe_abort r print f = 
  if !r then begin Myformat.printf "%a@." print f; exit 0; end
  
let parse_file ?prelude fn = 
  let ch = open_in fn in
  let close () = close_in ch in
  let buf = Lexing.from_channel ch in
  parse ?prelude buf close fn

let parse_string ?prelude ?(string="prelude") s = 
  let buf = Lexing.from_string s in
  parse ?prelude buf (fun () -> ()) string

let _ = 
  Options.update ();
  try
    let prelude = parse_string ~prelude:true Prelude.prelude in
    let ast = parse_file !Options.filename in
    let p = Parsetree.concat prelude ast in
    let p = Internalize.main p in
    maybe_abort Options.parse_only Ast.ParseT.print p;
    let p = Infer.infer p in
    maybe_abort Options.infer_only Ast.Infer.print p;
    let p = Infer.recon p in
    maybe_abort Options.constr_only Ast.Recon.print p;
    Typing.typing p;
    let p = Anf.normalize_term p in
    maybe_abort Options.anf_only Ast.Recon.print p;
    Typing.typing p;
    let p = Wp2.main p in
    maybe_abort Options.wp_only Ast.Recon.print p;
    Typing.formtyping p;
    let p = Simplify.allsimplify p in
    maybe_abort Options.simplify_only Ast.Recon.print p;
    p
(*
    Typing.formtyping p;
    let s = Sectionize.section p in
(*     maybe_abort Options.sectionize_only Sectionize.print s; *)
    Regen2.main (Sectionize.Flatten.main s)
*)
  with
  | Sys_error e -> Error.bad e
  | Infer.Error (s,loc) 
  | Typing.Error (s,loc) 
      -> Error.with_loc s loc 

