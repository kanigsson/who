(************************************************************************************)
(*                                                                                  *)
(*                      Who                                                         *)
(*                                                                                  *)
(*       A simple VCGen for higher-order programs.                                  *)
(*                                                                                  *)
(*  Copyright (C) 2009, 2010, Johannes Kanig                                        *)
(*  Contact: kanig@lri.fr                                                           *)
(*                                                                                  *)
(*  Who is free software: you can redistribute it and/or modify it under the terms  *)
(*  of the GNU Lesser General Public License as published by the Free Software      *)
(*  Foundation, either version 3 of the License, or any later version.              *)
(*                                                                                  *)
(*  Who is distributed in the hope that it will be useful, but WITHOUT ANY          *)
(*  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR   *)
(*  A PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more       *)
(*  details.                                                                        *)
(*                                                                                  *)
(*  You should have received a copy of the GNU Lesser General Public License along  *)
(*  with this program.  If not, see <http://www.gnu.org/licenses/>                  *)
(************************************************************************************)

let get def x = 
  match x with
  | None -> def
  | Some x -> x

let get_map def f x =
  match x with
  | None -> def
  | Some x -> f x

let map f x = 
  match x with
  | None -> None
  | Some x -> Some (f x)

let get_fail x = 
  match x with
  | Some x -> x
  | None -> assert false
