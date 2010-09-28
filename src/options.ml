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
let backend : [ `Coq | `Pangoline | `Why3 ] ref = ref `Pangoline
let sections = ref false
let suffix = ref ""
let verbose = ref false
let transform_only = ref false
let no_check = ref false

let transforms =
  ref (List.rev [
    ExtList.liftfun Anf.theory ;
    ExtList.liftfun Wp.theory ;
    ExtList.liftfun Tuples.theory;
    ExtList.liftfun InlineLet.theory ;
    ExtList.liftfun RemoveTuples.theory;
    ExtList.liftfun RemoveTrivialGoals.theory;
])

let append_trans x () = transforms := x :: !transforms
let append_simple_trans x () = transforms := ExtList.liftfun x :: !transforms

let touched = ref false

let clear () =
  transforms := [];
  touched := true

let print_version () =
  Format.printf "%s@." Version.version; exit 0

let opt_spec =
  Arg.align
  [
    "--parse-only", Arg.Set parse_only, " parse file and exit";
    "--transform-only", Arg.Set transform_only,
      " stop after applying transforms";
    "--no-check", Arg.Set no_check,
      " do not execute type checks after transforms";
    "--clear", Arg.Unit clear, " clear the list of transformations";
    "--anf", Arg.Unit (append_simple_trans Anf.theory),
      " apply anf normal form transformation";
    "--wp", Arg.Unit (append_simple_trans Wp.theory),
      " apply weakest precondition calculus";
    "--inlinelet", Arg.Unit (append_simple_trans InlineLet.theory),
      " inline let bindings";
    "--trivialgoals", Arg.Unit (append_simple_trans RemoveTrivialGoals.theory),
      " remove trivial goals";
    "--tuples", Arg.Unit (append_simple_trans Tuples.theory),
      " introduce tuples instead of maps";
    "--removetuples", Arg.Unit (append_simple_trans RemoveTuples.theory),
      " remove quantification over tuples";
    "--sectionize", Arg.Unit (append_simple_trans Sectionize.theory),
      " create sections and introduce vars and hypotheses";
    "--split-conj", Arg.Unit (append_simple_trans Split_conj.theory),
      " split conjunctions in goals";
    "--split-goals", Arg.Unit (append_trans Split_goals.theory),
      " put each goal in its own theory";
    "-o", Arg.Set_string outfile,
            "<arg> use <arg> instead of default filename for output";
    "--pangoline", Arg.Unit (fun () -> backend := `Pangoline),
            " set output format to pangoline";
    "--coq", Arg.Unit (fun () -> backend := `Coq),
            " set output format to Coq";
    "--why3", Arg.Unit (fun () -> backend := `Why3),
            " set output format to Why3";
    "--check-coq", Arg.Set check_coq, " check produced coq file using coqc";
    "--sections", Arg.Set sections, " when using Coq, do not split files";
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
    suffix :=
      match !backend with
      | `Why3 -> "_who.why"
      | `Pangoline -> "_who.pge"
      | `Coq -> "_who.v" in
  if !outfile = "" then outfile := base;
  (* update the transformation list; if the user has played with the list, he
   * has to do that by himself *)
  if !touched then ()
  else
    match !backend with
    | `Coq when !sections -> append_simple_trans Sectionize.theory ()
    | _ -> ()
(*
        append_simple_trans Split_conj.theory ();
        append_trans Split_goals.theory ();
        append_simple_trans Sectionize.theory ()
*)


