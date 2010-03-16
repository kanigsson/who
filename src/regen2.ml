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

let main s = 
  let f = !Options.outfile in
  let orig = f ^ ".orig" in
  if Sys.file_exists orig && Sys.file_exists f then begin
    (* recreation mode *)
    let orig_old = orig ^ ".old" in
    let bak = f ^ ".bak" in
    Cmd.cp orig orig_old;
    Cmd.cp f bak;
    Cmd.print_to_file `Coq orig s;
    Cmd.kdiff3 bak orig_old orig f
  end else begin 
    assert (not (Sys.file_exists f));
    (* creation mode *)
    Cmd.print_to_file `Coq orig s;
    Cmd.cp orig f;
    Cmd.chmod orig;
    if !Options.check_coq then begin
      Cmd.do_ (Myformat.sprintf "coqc %s" f);
      Cmd.rm orig; Cmd.rm f; 
      let basename = Filename.chop_extension f in
      Cmd.rm (basename ^ ".glob");
      Cmd.rm (basename ^ ".vo");
    end;
  end

