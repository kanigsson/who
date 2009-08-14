let filename = ref ""
let store_fn x = filename := x
let abort cin = close_in cin ; exit 1
let parse_only = ref false
let infer_only = ref false
let constr_only = ref false

open Infer

let opt_spec = 
  Arg.align
  [ 
    "-parse-only", Arg.Set parse_only, " parse file and exit";
    "-infer-only", Arg.Set infer_only, " parse file and exit";
    "-constr-only", Arg.Set constr_only, " do type inference and exit";
  ]
let () = 
  Arg.parse opt_spec store_fn "Usage: who <options> <file>"

let update () = 
  if !filename = "" then (Format.eprintf "No filename given"; exit(1))

let parse () = 
  let ch = open_in !filename in
  let buf = Lexing.from_channel ch in
  try 
    let prog = Parser.main Lexer.token buf in
    let () = close_in ch in
    prog
  with 
  | Parser.Error -> Format.eprintf "Parse error@."; abort ch
  | Lexer.Error msg -> Format.eprintf "lexer error@."; abort ch

let maybe_abort r print f = 
  if !r then begin Format.printf "%a@." print f; exit 0; end
  
let _ = 
  update ();
  let p = parse () in
  maybe_abort parse_only Ast.ParseT.print p;
  let p = Infer.infer p in
  maybe_abort infer_only Ast.Infer.print p;
  let p = Infer.recon p in
  maybe_abort constr_only Ast.Recon.print p;
  Typing.typing p

