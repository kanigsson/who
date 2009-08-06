let filename = ref ""
let store_fn x = filename := x
let abort cin = close_in cin ; exit 1
let parse_only = ref false
let intern_only = ref false
let constr_only = ref false

open Infer

let opt_spec = 
  Arg.align
  [ 
    "-parse-only", Arg.Set parse_only, " parse file and exit";
    "-intern-only", Arg.Set intern_only, " scope file, print reconversion and exit";
    "-constr-only", Arg.Set constr_only, " scope file, print reconversion and exit";
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
  | Parser.Error -> Format.eprintf "Parse error"; abort ch
  | Lexer.Error msg -> Format.eprintf "lexer error"; abort ch

let maybe_abort r print f = 
  if !r then begin Format.printf "%a@." print f; exit 0; end
  
let _ = 
  update ();
  let p = parse () in
  maybe_abort parse_only Ptree.print p;
  let p = Ptree.internalize p in
  maybe_abort intern_only Ast.print p;
(*
  let p = Generate.generate p in
  maybe_abort constr_only Constr.print p;
*)
  Infer.infer p

