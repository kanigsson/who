let parse ?(prelude=false) parser buf close fn = 
  if prelude then Options.prelude := true else Options.prelude := false;
  let abort () = close (); exit 1 in
  Lexer.reset buf;
  let prog = parser abort fn Lexer.token buf in
  prog

let maybe_abort r print f = 
  if !r then begin Myformat.printf "%a@." print f; exit 0; end
  
let parse_file ?prelude parser fn = 
  let ch, close =
    match fn with
    | None -> stdin, fun () -> ()
    | Some s -> 
        let ch = open_in s in
        ch, fun () -> close_in ch in
  let buf = Lexing.from_channel ch in
  parse ?prelude parser buf close fn

let parse_string ?prelude parser ?(string="prelude") s = 
  let buf = Lexing.from_string s in
  parse ?prelude parser buf (fun () -> ()) (Some string)

let annotparser abort fn token buf =
  try AnnotParser.main token buf
  with
  | AnnotParser.Error -> 
      Error.print_pos_error fn buf "Parse error"; abort ()
  | Lexer.Error msg -> 
        Error.print_pos_error fn buf 
          (Myformat.sprintf "Unexpected character: %s" msg);
        abort ()

let infer_parser abort fn token buf =
  try Parser.main token buf
  with
  | Parser.Error -> 
      Error.print_pos_error fn buf "Parse error"; abort ()
  | Lexer.Error msg -> 
        Error.print_pos_error fn buf 
          (Myformat.sprintf "Unexpected character: %s" msg);
        abort ()

let _ = 
  Options.update ();
  try
    let p = 
      if !Options.input_annot then
        let p = parse_file annotparser !Options.filename in
        AnnotInternalize.theory p
      else
        let prelude = parse_string ~prelude:true infer_parser Prelude.prelude in
        let ast = parse_file infer_parser !Options.filename in
        let p = prelude@ ast in
        let p = Internalize.theory p in
        maybe_abort Options.parse_only Ast.ParseT.print_theory p;
        let p = Infer.infer_th p in
        maybe_abort Options.infer_only Ast.Infer.print_theory p;
        let p = Infer.recon_th p in
        maybe_abort Options.constr_only Ast.Recon.print_theory p;
        p
    in
    Typing.theory p;
    p 
(*
    let p = Anf.term p in
    maybe_abort Options.anf_only Ast.Recon.print p;
    Typing.typing p;
    let p = Wp.main p in
    maybe_abort Options.wp_only Ast.Recon.print p;
    Typing.formtyping p;
    let p = Simplify.allsimplify p in
    maybe_abort Options.simplify_only Ast.Recon.print p;
    Typing.formtyping p;
    let kind = !Options.backend in
    let s = Sectionize.section kind p in
    let s = Sectionize.Flatten.main kind s in
    maybe_abort Options.sectionize_only (Sectionize.Flatten.print_all kind) s;
    if !Options.backend = `Coq then Regen2.main s else
      Pangoline.out s
*)
  with
  | Sys_error e -> Error.bad e
  | Infer.Error (s,loc) 
      -> Error.with_loc s loc 
(*
  | Typing.Error (s,loc) 
      -> Error.with_loc s loc 
*)

