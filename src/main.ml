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

let apply_one_trans f tl =
  if !Options.verbose then Myformat.printf "applying transformation...@?";
  let nt = List.flatten (List.map f tl) in
  if !Options.verbose then Myformat.printf "checking...@?";
  if !Options.no_check then () else List.iter Typing.theory nt;
  if !Options.verbose then Myformat.printf "done@.";
  nt

let apply_all_trans t =
  let t =
    if !Options.transforms = [] then begin Typing.theory t; [t] end
    else List.fold_right apply_one_trans !Options.transforms [t] in
  maybe_abort !Options.transform_only
    (Myformat.list Myformat.newline Ast.print_theory) t;
  t

let import input =
  let ast =
    match input with
    | `File fn -> parse_file infer_parser fn
    | `String s -> parse_string infer_parser s in
  let ast = Internalize.theory ast in
  let ast = Infer.theory ast in
  Recon.theory ast

let new_name () =
  Name.to_string (Name.from_string !Options.outfile)

let _ =
  Options.update ();
  try
    let p =
      if !Options.input_annot then
        let p = parse_file annotparser !Options.filename in
        AnnotInternalize.theory p
      else
        let prelude =
          if !Options.no_prelude then []
          else parse_string infer_parser Prelude.prelude in
        let user_text = parse_file infer_parser !Options.filename in
        let p = prelude @ user_text in
        let p = Internalize.theory p in
        let p = Infer.theory p in
        Recon.theory p in
    maybe_abort !Options.parse_only Ast.print_theory p;
    let l = apply_all_trans p in
    let l =
      match l with
      | [x] -> [!Options.outfile, x]
      | _ -> List.map (fun t -> new_name (), t) l in
    List.iter (fun (fn, t) ->
      let fn = fn ^ !Options.suffix in
      Cmd.print_to_file (!Options.backend :> Const.prover) fn t) l
  with
  | Sys_error e -> Error.bad e
  | Typing.Error (loc,e) -> Error.with_loc (Typing.explain e) loc
  | Infer.Error (loc,e) ->
      Error.with_loc (Infer.explain e) loc
  | Predefined.Error e -> Error.bad (Predefined.explain e)
  | Predefty.Error e -> Error.bad (Predefty.explain e)
  | CommonInternalize.Error (loc, e) ->
      Error.with_loc (CommonInternalize.explain e) loc
  | Recon.Error (loc,e) -> Error.with_loc (Recon.explain e) loc
  | Tuples.Error e -> Error.bad (Tuples.explain e)

