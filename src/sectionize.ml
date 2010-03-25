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

open Name
open Ast

module PL = Predefined.Logic
module G = Ty.Generalize

type outdecl = 
  | Decl of string 
  | Gen of Ty.Generalize.t
  | Infix of Name.t * int
  | Variable of Name.t * G.t * Ty.t * [`Logic | `Quant]
  | Type of Name.t * G.t
  | Axiom of Name.t * Ast.t
  | Section of Name.t * outdecl list
  | Import of string
  | PO of Name.t * Ast.t

let intro_eq f = function
  (* TODO PO could actually be used here *)
  | Gen _ | Variable _ | Type _ | Section _ | PO _ | Decl _ | Infix _ -> false
  | Axiom (_,x) -> equal x f
  | Import _ -> false

(* FIXME do something more intelligent for Pangoline infix notation *)
let is_infix_name n = 
  let s = Name.unsafe_to_string n in
  match s.[0] with
  | '=' | '!' | '+' | '-' | '*' | '<' | '>'  -> true
  | _ -> false

let to_section kind th = 
  let rec decl_to_outdecl d = 
    match d with
    | DLetReg _ | Program _ -> assert false
    | DGen g ->  [Gen g]
    | TypeDef (g,_,n) -> [Type (n,g)]
    | Formula (s,f, k) -> 
        begin match k with
        | `Assumed -> [Axiom (Name.from_string s,f)]
        | `Proved -> mk_Section ~namehint:s f
        end
    | Logic (x,g,t) -> 
        let decl = Variable (x,g,t, `Logic) in
        if is_infix_name x then [ Infix (x,0) ; decl ] else [decl]
    | Ast.Section (_,cl,th) -> 
        let choice = List.fold_left (fun acc (p,c) -> 
          if p = kind then c else acc) Const.TakeOver cl in
        begin match choice with
        | Const.Predefined -> []
        | Const.Include f -> [ Import f ]
        | Const.TakeOver -> List.flatten (List.map decl_to_outdecl th)
        end
  and term_intro (f : Ast.t) : outdecl list * Ast.t = 
    (* take a formula and cut it into two parts : intro and the rest *)
    let rec aux acc f = 
      match f.v with
      | Quant (`FA, t,b) ->
          let x , f = vopen b in
          aux (Variable (x,Ty.Generalize.empty,t,`Quant) :: acc) f
      | Ast.Gen (g,f) -> 
          if Ty.Generalize.is_empty g then aux acc f
          else aux ((Gen g)::acc) f
      | f' -> 
          match destruct_app2_var' f' with
          | Some (v,_,f1,f2) when PL.equal v PI.impl_id  -> 
              aux (Axiom (Name.from_string "H", f1)::acc) f2
          | _ -> List.rev acc, f in
    aux [] f
  and make_PO ?(namehint="goal") ( f : Ast.t) : outdecl list = 
    let rec aux acc f = 
      match f.v with
      | Quant (`FA,_,_) | Ast.Gen _ ->
          mk_Section f @ acc
      | f' ->
          match destruct_app2_var' f' with
          | Some (v,_,_,_) when PL.equal v PI.impl_id -> mk_Section f @ acc
          | Some (v,_,f1,f2) when PL.equal v PI.and_id -> aux (aux acc f2) f1
          | _ -> PO (Name.from_string namehint, f) :: acc
    in
    aux [] f
  and mk_Section ?namehint (f : Ast.t) :outdecl list = 
    let il, f' = term_intro f in
    match make_PO ?namehint f' with
    | [] -> []
    | [x] when List.length il = 0 -> [x]
    | l -> [Section (Name.from_string "sec", il@l)]
  in
  List.flatten (List.map decl_to_outdecl th)

let to_coq_decls th = 
  let aux d = 
    match d with
    | Import f -> Decl (Printf.sprintf "Require Import %s." f)
    | _ -> d in
  Decl "Set Implicit Arguments." :: List.map aux th

open Myformat

let lname s fmt l = 
  if l = [] then () else
  fprintf fmt "(%a :@ %s)" (print_list space Name.print) l s

let intro_name s fmt l = 
  if l = [] then () else
  fprintf fmt "Variables %a :@ %s.@ " (print_list space Name.print) l s

let pr_generalize in_term kind fmt ((tl,rl,el) as g) = 
  if Ty.Generalize.is_empty g then ()
  else
    let in_term fmt = if in_term then pp_print_string fmt "type" else () in
    match kind with
    | `Coq -> 
        fprintf fmt "forall@ %a@ %a@ %a,@ "
        (lname "Type") tl (lname "key") rl (lname "kmap") el
    | `Pangoline -> 
        fprintf fmt "forall %t %a." in_term (print_list space Name.print) tl

let def kind fmt x = 
  match kind, x with
  | `Coq, `Quant -> pp_print_string fmt "Variable"
  | `Coq, `Logic -> pp_print_string fmt "Definition"
  | `Pangoline, _ -> pp_print_string fmt "logic"

let hypo fmt = function
  | `Pangoline -> pp_print_string fmt "hypothesis"
  | `Coq -> pp_print_string fmt "Hypothesis"
let lemma fmt = function
  | `Pangoline -> pp_print_string fmt "lemma"
  | `Coq -> pp_print_string fmt "Lemma"

let print_stop fmt = function
  | `Pangoline -> ()
  | `Coq -> pp_print_string fmt "."

let print_proof fmt = function
  | `Pangoline -> ()
  | `Coq -> fprintf fmt "@\nProof.@\nAdmitted.@\n"

let print_def_end kind fmt x = 
  match x with
  | `Quant -> ()
  | `Logic -> print_proof fmt kind

type sup = [`Coq | `Pangoline | `Who ]

let beginsec kind fmt n = 
  match kind with
  | `Pangoline -> pp_print_string fmt "begin"
  | `Coq -> fprintf fmt "Section %a." Name.print n

let endsec kind fmt n = 
  match kind with
  | `Pangoline -> pp_print_string fmt "end"
  | `Coq -> fprintf fmt "End %a." Name.print n

let rec print kind fmt = function
  | Decl s -> fprintf fmt "%s" s
  | Import _ -> assert false
  | Section (n,l) ->
      fprintf fmt "@[<hov 2>%a@\n %a@] %a" 
        (beginsec kind) n (theory kind) l (endsec kind) n
  | Gen (tl,rl,el) -> 
      begin match kind with
      | `Coq ->
          fprintf fmt "%a%a%a"
          (intro_name "Type") tl (intro_name "key") rl (intro_name "kmap") el
      | `Pangoline ->
          print_list newline (fun fmt s -> 
            fprintf fmt "type (0) %a" Name.print s) fmt tl
      end
  | Variable (x,g,t,k) -> 
      let npr fmt n = 
        match kind with 
        | `Pangoline when is_infix_name n -> fprintf fmt "( %a )" Name.print n
        | _ -> Name.print fmt n in
      fprintf fmt "@[<hov 2>%a %a:@ %a %a%a%a @]" (def kind) k npr x
        (pr_generalize false kind) g 
          (Ty.gen_print ~kind:(kind :> sup)) t print_stop kind
        (print_def_end kind) k
  | Axiom (h,e) -> 
      fprintf fmt "@[<hov 2>%a %a:@ %a%a @]" hypo kind Name.print h 
        (Ast.gen_print (kind :> sup)) e print_stop kind
  | PO (x,e) -> 
      fprintf fmt "@[<hov 2>%a %a:@ %a%a%a@]" lemma kind Name.print x 
        (Ast.gen_print (kind :> sup)) e 
          print_stop kind print_proof kind
  | Infix (n,i) ->
      if kind = `Pangoline then fprintf fmt "infix %a %d" Name.print n i
  | Type (x,((tl,_,_) as g)) -> 
      begin match kind with
      | `Coq ->
          fprintf fmt "@[<hov 2>Definition %a :@ %a%s. @]" Name.print x 
            (pr_generalize true `Coq) g "Type"
      | `Pangoline ->
          fprintf fmt "@[<hov 2> type (%d) %a @]" (List.length tl) Name.print x
      end
and theory kind fmt l = print_list newline (print kind) fmt l

let print_all kind fmt l = 
  let l = 
    match kind with
    | `Coq -> to_coq_decls l
    | _ -> l in
  theory kind fmt l
