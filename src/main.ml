let parse p buf close fn = 
  let abort () = close (); exit 1 in
  Lexer.reset buf;
  let prog = p abort fn Lexer.token buf in
  prog

let maybe_abort r print f = 
  if !r then begin Myformat.printf "%a@." print f; exit 0; end
  
let parse_file p fn = 
  let ch, close =
    match fn with
    | None -> stdin, fun () -> ()
    | Some s -> 
        let ch = open_in s in
        ch, fun () -> close_in ch in
  let buf = Lexing.from_channel ch in
  parse p buf close fn

let parse_string p ?(string="prelude") s = 
  let buf = Lexing.from_string s in
  parse p buf (fun () -> ()) (Some string)

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

let apply_one_trans f t = 
  if !Options.verbose then Myformat.printf "applying transformation...@?";
  let nt = f t in
  if !Options.verbose then Myformat.printf "checking...@?";
  if !Options.no_check then () else Typing.theory nt; 
  if !Options.verbose then Myformat.printf "done@.";
  nt

let apply_all_trans t = 
  let t = 
    if !Options.transforms = [] then begin Typing.theory t; t end
    else List.fold_right apply_one_trans !Options.transforms t in
  maybe_abort Options.transform_only Ast.Recon.print_theory t;
  t

let _ = 
  Options.update ();
  try
    let p = 
      if !Options.input_annot then
        let p = parse_file annotparser !Options.filename in
        let p = AnnotInternalize.theory p in
        maybe_abort Options.parse_only Ast.Recon.print_theory p;
        p
      else
        let prelude = 
          if !Options.no_prelude then []
          else parse_string infer_parser Prelude.prelude in
        let ast = parse_file infer_parser !Options.filename in
        let p = prelude@ ast in
        let p = Internalize.theory p in
        maybe_abort Options.parse_only Ast.ParseT.print_theory p;
        let p = Infer.infer_th p in
        maybe_abort Options.infer_only Ast.Infer.print_theory p;
        let p = Infer.recon_th p in
        p
    in
    let p = apply_all_trans p in
    let kind = !Options.backend in
    let s = Sectionize.to_section kind p in
    if !Options.backend = `Coq then Regen2.main s else Pangoline.out s
  with
  | Sys_error e -> Error.bad e
  | Infer.Error (s,loc) 
  | Typing.Error (s,loc) 
      -> Error.with_loc s loc 

