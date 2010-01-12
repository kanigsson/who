open Name
open Ast

module PL = Predefined.Logic
module G = Ty.Generalize

type outdecl = 
  | Decl of string 
  | Gen of Ty.Generalize.t
  | Variable of Name.t * G.t * Ty.t * [`Logic | `Quant]
  | Type of Name.t * G.t
  | Axiom of Name.t * G.t *  Ast.Recon.t
  | Section of Name.t * outdecl list
  | BeginSec of Name.t
  | EndSec of Name.t
  | Import of string
  | PO of Name.t * Ast.Recon.t

let intro_eq f = function
  (* TODO PO could actually be used here*)
  | Gen _ | Variable _ | Type _ | Section _ | PO _ | Decl _ 
  | BeginSec _ | EndSec _ -> false
  | Axiom (_,g,x) when Ty.Generalize.is_empty g -> equal x f
  | Axiom _ | Import _ -> false

let to_section kind th = 
  let rec decl_to_outdecl d = 
    match d with
    | DLetReg _ | Program _ -> assert false
    | TypeDef (g,_,n) -> [Type (n,g)]
    | Formula (s,f, k) -> 
        begin match k with
        | `Assumed -> [Axiom (Name.from_string s,G.empty,f)]
        | `Proved -> mk_Section ~namehint:s f
        end
    | Logic (x,g,t) -> [ Variable (x,g,t, `Logic)]
    | Ast.Section (_,cl,th) -> 
        let choice = List.fold_left (fun acc (p,c) -> 
          if p = kind then c else acc) Const.TakeOver cl in
        begin match choice with
        | Const.Predefined -> []
        | Const.Include f -> [ Import f ]
        | Const.TakeOver -> List.flatten (List.map decl_to_outdecl th)
        end
  and term_intro (f : Ast.Recon.t) : outdecl list * Ast.Recon.t = 
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
          | Some (v,_,f1,f2) when Name.equal v PL.impl_var  -> 
              aux (Axiom (Name.from_string "H",G.empty, f1)::acc) f2
          | _ -> List.rev acc, f in
    aux [] f
  and make_PO ?(namehint="goal") ( f : Ast.Recon.t) : outdecl list = 
    let rec aux acc f = 
      match f.v with
      | Quant (`FA,_,_) | Ast.Gen _ ->
          mk_Section f @ acc
      | f' ->
          match destruct_app2_var' f' with
          | Some (v,_,_,_) when Name.equal v PL.impl_var -> mk_Section f @ acc
          | Some (v,_,f1,f2) when Name.equal v PL.and_var -> aux (aux acc f2) f1
          | _ -> PO (Name.from_string namehint, f) :: acc
    in
    aux [] f
  and mk_Section ?namehint (f : Ast.Recon.t) :outdecl list = 
    let il, f' = term_intro f in
    match make_PO ?namehint f' with
    | [] -> []
    | [x] when List.length il = 0 -> [x]
    | l -> [Section (Name.from_string "sec", il@l)]
  in
  List.flatten (List.map decl_to_outdecl th)

let rec flatten th = List.flatten (List.map decl th)
and decl d = 
  match d with
  | Section (n,dl) -> BeginSec n :: (flatten dl @ [ EndSec n ] )
  | _ -> [d]

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

let print kind fmt = function
  | Decl s -> fprintf fmt "%s" s
  | Import _ | Section _ -> assert false
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
      fprintf fmt "@[<hov 2>%a %a:@ %a %a%a%a @]" (def kind) k Name.print x
        (pr_generalize false kind) g (Ty.gen_print (kind :> sup)) t print_stop kind
        (print_def_end kind) k
  | Axiom (h,g,e) -> 
      fprintf fmt "@[<hov 2>%a %a:@ %a %a%a @]" hypo kind Name.print h 
        (pr_generalize true kind) g (Ast.Recon.gen_print (kind :> sup)) e print_stop kind
  | PO (x,e) -> 
      fprintf fmt "@[<hov 2>%a %a:@ %a%a%a@]" lemma kind Name.print x 
        (Ast.Recon.gen_print (kind :> sup)) e print_stop kind print_proof kind
  | Type (x,((tl,_,_) as g)) -> 
      begin match kind with
      | `Coq ->
          fprintf fmt "@[<hov 2>Definition %a :@ %a%s. @]" Name.print x 
            (pr_generalize true `Coq) g "Type"
      | `Pangoline ->
          fprintf fmt "@[<hov 2> type (%d) %a @]" (List.length tl) Name.print x
      end
  | BeginSec n -> 
      if kind = `Coq then fprintf fmt "@[<hov 2>Section %a." Name.print n
  | EndSec n -> 
      if kind = `Coq then fprintf fmt "@]End %a." Name.print n

let print_all kind fmt l = 
  let l = 
    match kind with
    | `Coq -> to_coq_decls l
    | _ -> l
  in
  print_list newline (print kind) fmt l
