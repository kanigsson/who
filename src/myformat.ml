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

include Format

type 'a fmt = Format.formatter -> 'a -> unit

let rec list sep prf fmt = function
  | [] -> ()
  | [x] -> prf fmt x
  | (x::xs) -> prf fmt x; sep fmt (); list sep prf fmt xs

let int = pp_print_int
let string = pp_print_string

let comma fmt () = string fmt ","
let semi fmt () = string fmt ";"
let space fmt () = fprintf fmt "@ "
let break fmt () = fprintf fmt "@,"
let fullstop fmt () = fprintf fmt "@."
let nothing _ () = ()
let double_newline fmt () = fprintf fmt "@\n@\n"
let newline fmt () = fprintf fmt "@\n"
let lbrack fmt () = string fmt "["
let rbrack fmt () = string fmt "]"


let optlist pr fmt = function
  | [] -> space fmt ()
  | l -> fprintf fmt "@ [%a]@ " (list space pr) l

let opt_print prf fmt = function
  | None -> ()
  | Some x -> prf fmt x

let pr_opt_string fmt s = opt_print string fmt s

let ksprintf k s =
  ignore(flush_str_formatter ());
  kfprintf (fun _ -> k (flush_str_formatter ())) str_formatter s

let sprintf s = ksprintf Misc.id s

let print_set fmt s = 
  Misc.SS.iter (fun x -> string fmt x ; space fmt ()) s


let hash_print ?(bsep=lbrack) ?(endsep=rbrack) prk prv fmt h =
  bsep fmt ();
  Hashtbl.iter (fun k v -> fprintf fmt "%a|->%a;" prk k prv v) h;
  endsep fmt ()

let paren pr fmt x = fprintf fmt "(%a)" pr x

let print_string_map pr fmt m = 
  Misc.StringMap.iter (fun x v -> fprintf fmt "%s : %a" x pr v ) m;
  fprintf fmt "@."
