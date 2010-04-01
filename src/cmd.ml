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

open Myformat

let do_ s = 
  printf "%s@." s;
  ignore (Sys.command s)
let chmod f = do_ (sprintf "chmod a-w %s" f)  
let cp f1 f2 = do_ (sprintf "cp %s %s" f1 f2)
let rm f = do_ (sprintf "rm -f %s" f)  

let pangoline f = do_ (sprintf "pangoline %s" f)

let print_to_file kind f s = 
  let c = open_out f in
  let fmt = formatter_of_out_channel c in
  Ast.Print.theory ~kind fmt s;
  close_out c

let diff3 myfile oldfile yourfile output =
  do_ (sprintf "diff3 -m %s %s %s > %s" myfile oldfile yourfile output)

let kdiff3 myfile oldfile yourfile output =
  do_ (sprintf "kdiff3 --auto %s %s %s -o %s" oldfile myfile yourfile output)

