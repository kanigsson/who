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

open Myformat
open Lexing

let bad s = eprintf "%s@." s; exit(1)

let error fn l c s = 
  let fn = Opt.get "stdin" fn in
  eprintf "%s: line %d char %d : %s @." fn l c s

let print_pos_error fn buf s =
  let p = buf.lex_curr_p in
  let l = p.pos_lnum in
  let c = p.pos_cnum - p.pos_bol in
    error fn l c s

let with_loc msg {Loc.st = (sta,stb); en = _} = 
  error !Options.filename sta stb msg; exit(1)

let mismatch f1 f2 arg1 arg2 t1 t2 = 
  sprintf "%s is of type %a, but %s is of type %a" arg1 f1 t1 arg2 f2 t2

let ty_mismatch = mismatch Ty.print Ty.print
let ty_app_mismatch = ty_mismatch "expression" "function argument"

(*
let incompatible_subst = "incompatible substitution attempted"
let effect_inst_nbr = "invalid number of effect instantiations" 

let fty_mismatch = mismatch Fty.print Fty.print

let lty_mismatch = mismatch Lty.print Lty.print

let ty_rec_mismatch = ty_mismatch "recursive function" "declaration"
let ty_aff_mismatch = ty_mismatch "expression" "reference"
let fty_app_mismatch = fty_mismatch "expression" "function argument"
let fty_form_mismatch = fty_mismatch "formula" "expected formula"

let fty_rec_mismatch = fty_mismatch "formula" "reference"
let fty_eq_mismatch = 
  fty_mismatch "left argument of equality" "right argument"

let ty_fty_app_mismatch = 
  mismatch Ty.print Fty.print "expression" "function argument"

let lty_eq_mismatch = 
  lty_mismatch "left argument of equality" "right argument"
let lty_form_mismatch = lty_mismatch "formula" "expected formula"
let lty_app_mismatch = lty_mismatch "expression" "function argument"

let branch_mismatch = ty_mismatch "first branch" "second branch"
let condition_bool = "condition is not of type bool"

let for_int = "limits of for loop are not of type int"
let for_unit = "body of for loop is not of type unit"

let not_a_function = "expression is not a function"
let fnot_a_function f t = 
  mysprintf "formula %a is not of function type but of type : %a" 
    Formula.print f Fty.print t

let generalization = "Generalization attempted for non-value"

let unbound_id s v = mysprintf "unknown %s identifier : %a@." s Name.print v
let unbound_string s v = mysprintf "unknown %s identifier : %s@." s v

let pure_formulas = "all values of pure type should be formulas"

let label_not_contain l = 
  mysprintf "label %a does not contain ref %a" Formula.print l

let label_not_contain_r l r = label_not_contain l RVar.print r
let label_not_contain_e l e = label_not_contain l EffVar.print e

let not_a_label x = 
  mysprintf "variable %a is not of label type" Formula.print x

let not_type_prop s = mysprintf "%s is not of type prop" s

let negation_prop = not_type_prop "argument of negation"
let conjunction_prop = not_type_prop "arguments of conjunction"
let imply_prop = not_type_prop "arguments of implication"
let forall_ex_prop = not_type_prop "argument of quantification"


let not_tuple_type = "not a tuple type"

let not_of_reftype e = 
  mysprintf "not of reference type: %a" Itree.print e

let not_of_reftype_v e = 
  mysprintf "not of reference type: %a" Anf.print_val_node e

let illformed_ty t = 
  mysprintf "illformed type: %a" Ty.print t

let illformed_fty t = 
  mysprintf "illformed type: %a" Fty.print t

let effects_not_subset e1 e2 = 
  mysprintf "%a is not a subset of %a" Effect.print e1 Effect.print e2
*)
