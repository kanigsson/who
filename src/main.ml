(******************************************************************************)
(*                                                                            *)
(*                      Who                                                   *)
(*                                                                            *)
(*       A simple VCGen for higher-order programs.                            *)
(*                                                                            *)
(*  Copyright (C) 2009, 2010, Johannes Kanig                                  *)
(*  Contact: kanig@lri.fr                                                     *)
(*                                                                            *)
(*  Who is free software: you can redistribute it and/or modify it under the  *)
(*  terms of the GNU Lesser General Public License as published by the Free   *)
(*  Software Foundation, either version 3 of the License, or any later        *)
(*  version.                                                                  *)
(*                                                                            *)
(*  Who is distributed in the hope that it will be useful, but WITHOUT ANY    *)
(*  WARRANTY; without even the implied warranty of MERCHANTABILITY or         *)
(*  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public      *)
(*  License for more details.                                                 *)
(*                                                                            *)
(*  You should have received a copy of the GNU Lesser General Public License  *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>      *)
(******************************************************************************)

open Tuples

let parse p buf close fn =
  let abort () = close (); exit 1 in
  Lexer.reset buf;
  let prog = p abort fn Lexer.token buf in
  prog

let maybe_abort r print f =
  if r then begin Myformat.printf "%a@." print f; exit 0; end

let parse_file p fn =
  let ch, close =
    match fn with
    | None -> stdin, fun () -> ()
    | Some s ->
        let ch = open_in s in
        ch, fun () -> close_in ch in
  let buf = Lexing.from_channel ch in
  parse p buf close fn

let parse_string p s =
  let buf = Lexing.from_string s in
  parse p buf (fun () -> ()) (Some "prelude")

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
  maybe_abort !Options.transform_only Ast.Recon.print_theory t;
  t

let import parse_only infer_only input =
  let ast =
    match input with
    | `File fn -> parse_file infer_parser fn
    | `String s -> parse_string infer_parser s in
  let ast = Internalize.theory ast in
  maybe_abort parse_only Ast.ParseT.print_theory ast;
  let ast = Infer.infer_th ast in
  maybe_abort infer_only Ast.Infer.print_theory ast;
  Infer.recon_th ast

let _ =
  Options.update ();
  try
    let p =
      if !Options.input_annot then
        let p = parse_file annotparser !Options.filename in
        let p = AnnotInternalize.theory p in
        maybe_abort !Options.parse_only Ast.Recon.print_theory p;
        p
      else
        let prelude =
          if !Options.no_prelude then []
          else
            let p = import false false (`String Prelude.prelude) in
            Predefined.Logic.init (Ast.Recon.build_symbol_table p);
            p in
        let user_input =
          import !Options.parse_only !Options.infer_only
            (`File !Options.filename) in
        prelude @ user_input
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

