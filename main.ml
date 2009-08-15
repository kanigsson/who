let parse () = 
  let ch = open_in !Options.filename in
let abort () = close_in ch ; exit 1 in
  let buf = Lexing.from_channel ch in
  try 
    let prog = Parser.main Lexer.token buf in
    let () = close_in ch in
    prog
  with 
  | Parser.Error -> 
      Error.print_pos_error buf "Parse error"; abort ()
  | Lexer.Error msg -> 
        Error.print_pos_error buf 
          (Format.sprintf "Unexpected character: %s" msg);
        abort ()

let maybe_abort r print f = 
  if !r then begin Format.printf "%a@." print f; exit 0; end
  
let _ = 
  Options.update ();
  try
    let p = parse () in
    maybe_abort Options.parse_only Ast.ParseT.print p;
    let p = Infer.infer p in
    maybe_abort Options.infer_only Ast.Infer.print p;
    let p = Infer.recon p in
    maybe_abort Options.constr_only Ast.Recon.print p;
    Typing.typing p
  with
  | Sys_error e -> Error.bad e
  | Infer.Error (s,loc) -> Error.with_loc s loc

