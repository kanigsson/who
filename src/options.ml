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
let backend : [ `Coq | `Pangoline ] ref = ref `Pangoline
let suffix = ref ""
let verbose = ref false
let transform_only = ref false
let no_check = ref false

let splitfun = ref (fun x -> [x])

let transforms =
  ref (List.rev [
    Anf.theory ;
    Wp.theory ;
    Tuples.theory;
    InlineLet.theory ;
    RemoveTuples.theory;
    RemoveTrivialGoals.theory;
])

let append_trans x () = transforms := x :: !transforms

let clear () = transforms := []

let print_version () =
  Format.printf "%s@." Version.version; exit 0

let opt_spec =
  Arg.align
  [
    "--input-annot", Arg.Set input_annot,
      " take fully type annotated input file";
    "--parse-only", Arg.Set parse_only, " parse file and exit";
    "--transform-only", Arg.Set transform_only,
      " stop after applying transforms";
    "--no-check", Arg.Set no_check,
      " do not execute type checks after transforms";
    "--clear", Arg.Unit clear, " clear the list of transformations";
    "--anf", Arg.Unit (append_trans Anf.theory),
      " apply anf normal form transformation";
    "--wp", Arg.Unit (append_trans Wp.theory),
      " apply weakest precondition calculus";
    "--inlinelet", Arg.Unit (append_trans InlineLet.theory),
      " inline let bindings";
    "--trivialgoals", Arg.Unit (append_trans RemoveTrivialGoals.theory),
      " remove trivial goals";
    "--tuples", Arg.Unit (append_trans Tuples.theory),
      " introduce tuples instead of maps";
    "--removetuples", Arg.Unit (append_trans RemoveTuples.theory),
      " remove quantification over tuples";
    "--sectionize", Arg.Unit (append_trans Sectionize.theory),
      " build sections to share context between goals";
    "--desectionize", Arg.Unit (fun () -> splitfun := Desectionize.theory),
      " each context goes to one file";
    "--split-goals", Arg.Unit (fun () -> splitfun := Split_goals.theory),
      " split goals with conjunctions and put each goal in one file";
    "-o", Arg.Set_string outfile,
            "<arg> use <arg> instead of default filename for output";
    "--pangoline", Arg.Unit (fun () -> backend := `Pangoline),
            " set output format to pangoline";
    "--coq", Arg.Unit (fun () -> backend := `Coq),
            " set output format to Coq";
    "--check-coq", Arg.Set check_coq, " check produced coq file using coqc";
    "--noprelude", Arg.Set no_prelude, " do not add a prelude to the file";
    "-v", Arg.Set verbose, " be verbose";
    "--verbose", Arg.Set verbose, " be verbose";
    "--version", Arg.Unit print_version , " print version information and exit";
  ]

let () = Arg.parse opt_spec store_fn "Usage: who <options> <file>"

let update () =
  let base =
    match !filename with
    | None -> "base"
    | Some s -> Filename.chop_extension s in
  let () =
    suffix := match !backend with | `Pangoline -> ".pge" | `Coq -> ".v" in
  if !outfile = "" then outfile := Myformat.sprintf "%s_who" base
