open Name
open Ast

type intro = 
  | Gen of Ty.Generalize.t
  | Variable of Name.t * Ty.Generalize.t * Ty.t * [`Logic | `Quant]
  | Type of Name.t * Ty.Generalize.t
  | Hypo of Name.t * Ast.Recon.t
  | Axiom of Name.t * Ty.Generalize.t *  Ast.Recon.t
  | Import of string
(*   | WhoSection of string * string option *)
type section = 
  | Empty
  | PO of Name.t * Ast.Recon.t
  | Section of Name.t * intro list * section list


let intro_eq f = function
  | Gen _ | Variable _ | Type _  -> false
  | Hypo (_,x) -> equal x f
  | Axiom (_,g,x) when Ty.Generalize.is_empty g -> equal x f
  | Axiom _ | Import _ -> false

let rec skip_till_end x = 
  match x.v with
  | EndSec e -> e
  | Let (_,_,_,b,_) -> 
      let _,f = sopen b in
      skip_till_end f
  | TypeDef (_,_,_,e) -> skip_till_end e
  | _ -> assert false

let section kind f = 
  let rec section f =
    let il, f' = intro f in
    match prove il f' with
    | [] -> Empty
    | [x] when List.length il = 0 -> x
    | l -> Section (Name.from_string "sec", il,l)

  and intro f = 
    let rec aux acc f = 
      match f.v with
      | Quant (`FA, t,b) ->
          let x , f = vopen b in
          aux ( Variable (x,Ty.Generalize.empty,t,`Quant) :: acc) f
      | Ast.Gen (g,f) -> 
          if Ty.Generalize.is_empty g then aux acc f
          else aux ((Gen g)::acc) f
      | Let (_,_,{v = Logic _}, ((_,{name = Some 
      ("!=" | "!!" | "==" | "<<" | "<<=" | ">>" | ">>=" | "empty" )},_) as b) ,_)
      -> 
        let _,f = sopen b in
        aux acc f
      | Let (_,g,{v = Logic t},b,_) ->
          let x, f = sopen b in
          aux (Variable (x,g,t, `Logic)::acc) f
      | Let (_,g,{v = Ast.Axiom a},b,_) ->
          let x, f = sopen b in
          aux (Axiom (x,g,a)::acc) f
      | TypeDef (g,_,x,e) -> 
          aux (Type (x,g)::acc) e
      | Ast.Section (_,f,e) ->
          let choice = List.fold_left (fun acc (p,c) -> 
            if p = kind then c else acc) Const.TakeOver f in
          begin match choice with
          | Const.Predefined -> aux acc (skip_till_end e)
          | Const.Include f -> aux (Import f :: acc) (skip_till_end e)
          | Const.TakeOver -> aux acc e
          end
      | f' -> 
          match destruct_app2_var' f' with
          | Some ({name = Some "->"},_,f1,f2) -> 
              aux (Hypo (Name.from_string "H", f1)::acc) f2
          | _ -> List.rev acc, f in
    aux [] f

  and prove ctx f =
    let rec aux acc f =
      match f.v with
      | Quant (`FA,_,_) | Ast.Gen _
      | TypeDef _
      | Let (_,_,{v = Logic _},_,_)
      | Let (_,_,{v = Ast.Axiom _},_,_) ->
          begin match section f with
          | Empty -> acc
          | s -> s::acc
          end
      | f' ->
          match destruct_app2_var' f' with
          | Some ({name = Some "->"},_,_,_) ->
              begin match section f with
              | Empty -> acc
              | s -> s::acc
              end
          | Some ({name = Some "/\\"},_,f1,f2) -> aux (aux acc f2) f1
          | _ -> 
              if List.exists (intro_eq f) ctx then acc
              else PO (Name.from_string "goal", f) :: acc
    in
    aux [] f
  in
  section f

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
        fprintf fmt "forall %t %a" in_term (print_list space Name.print) tl

(*
let pr_intro fmt = function
  | Gen (tl,rl,el) -> 
      fprintf fmt "%a%a%a"
      (intro_name "Set") tl (intro_name "key") rl (intro_name "kmap") el
  | Variable (x,g,t) -> 
      fprintf fmt "@[<hov 2>Variable %a:@ %a%a. @]" 
      Name.print x pr_generalize g Ty.cprint t
  | Hypo (h,e) -> 
      fprintf fmt "@[Hypothesis %a:@ %a. @]" 
        Name.print h Ast.Recon.cprint e
  | Axiom (x,g,t) -> 
      fprintf fmt "@[Axiom %a: %a %a. @]" Name.print x 
        pr_generalize g Ast.Recon.cprint t
  | Type (x,g) -> 
      fprintf fmt "@[Parameter %a :@ %a%s. @]" Name.print x pr_generalize g "Set"

let rec print fmt = function
  | Empty -> ()
  | PO (x,e) -> 
      fprintf fmt "@[Lemma %a:@ %a.@]@," Name.print x 
        Ast.Recon.cprint e
  | Section (x,il,sl) -> 
      fprintf fmt "@,@[<hov 2>Section %a.@\n%a@\n%a@]@\nEnd %a."
        Name.print x (print_list pp_force_newline pr_intro) il 
          (print_list pp_force_newline print) sl
        Name.print x

let print_decls fmt () = 
  fprintf fmt "Set Implicit Arguments.@\n";
  fprintf fmt "Require Import WhoMap.@\n";
  fprintf fmt "Require Import ZArith.@\n";
  fprintf fmt "Open Scope Z_scope.@\n";
  fprintf fmt "Require Omega.@\n";
  fprintf fmt "Variable ref : forall (a : Type) (k : key), Type.@\n";
  fprintf fmt "Definition ___get (A : Type) (k : key) (r : ref A k) (m : kmap) :=
    __get A k m.@\n";
  fprintf fmt "Notation \"!!\" := (___get) (at level 50).@\n";
*)

(*
let print_all fmt s = 
  print_decls fmt ();
  print fmt s;
  pp_print_flush fmt ()
*)

module Flatten = struct

  type t = 
    | FCoqDecl of string * Name.t
    | FGen of Ty.Generalize.t
    | FVariable of Name.t * Ty.Generalize.t * Ty.t * [`Logic | `Quant]
    | FType of Name.t * Ty.Generalize.t
    | FAxiom of Name.t * Ty.Generalize.t *  Ast.Recon.t
    | FPO of Name.t * Ast.Recon.t
    | FBeginSec of Name.t
    | FEndSec of Name.t

  let name_of_string s = 
    let n = try String.index s ' ' with Not_found -> String.length s - 1 in
    let n = min 10 n in
    Name.from_string (String.sub s 0 n)

  let intro = function
    | Gen g -> FGen g
    | Variable (n,g,t,k) -> FVariable (n,g,t,k)
    | Type (n,t) -> FType (n,t)
    | Hypo (n,e) -> FAxiom (n,([],[],[]),e)
    | Axiom (n,g,e) -> FAxiom (n,g,e)
    | Import f -> 
        FCoqDecl (sprintf "Require Import %s" f, name_of_string f)

  let rec section x acc = 
    match x with
    | Empty -> acc
    | PO (n,e) -> FPO (n,e) :: acc
    | Section (n,il,sl) -> 
        FBeginSec n ::
          List.fold_right
            (fun x acc -> intro x :: acc) il
            (List.fold_right section sl (FEndSec n :: acc))

  let coqdecls = 
    List.map (fun s -> FCoqDecl (s, name_of_string s))
      [ "Set Implicit Arguments"; ]

  let main kind s = 
    let s = section s [] in
    if s = [] then [] else 
      if kind = `Coq then coqdecls @ s else s

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

  type sup = [`Coq | `Pangoline | `Who ]
  let print kind fmt = function
    | FCoqDecl (s,_) -> fprintf fmt "%s." s
    | FGen (tl,rl,el) -> 
        begin match kind with
        | `Coq ->
            fprintf fmt "%a%a%a"
            (intro_name "Type") tl (intro_name "key") rl (intro_name "kmap") el
        | `Pangoline ->
            print_list newline (fun fmt s -> 
              fprintf fmt "type (0) %a" Name.print s) fmt tl
        end
    | FVariable (x,g,t,k) -> 
        fprintf fmt "@[<hov 2>%a %a:@ %a. %a%a @]" (def kind) k Name.print x
          (pr_generalize false kind) g (Ty.gen_print (kind :> sup)) t print_stop kind
    | FAxiom (h,g,e) -> 
        fprintf fmt "@[<hov 2>%a %a:@ %a. %a%a @]" hypo kind Name.print h 
          (pr_generalize true kind) g (Ast.Recon.gen_print (kind :> sup)) e print_stop kind
    | FPO (x,e) -> 
        fprintf fmt "@[<hov 2>%a %a:@ %a%a@]" lemma kind Name.print x 
          (Ast.Recon.gen_print (kind :> sup)) e print_stop kind
    | FType (x,((tl,_,_) as g)) -> 
        begin match kind with
        | `Coq ->
            fprintf fmt "@[<hov 2>Definition %a :@ %a%s. @]" Name.print x 
              (pr_generalize true `Coq) g "Type"
        | `Pangoline ->
            fprintf fmt "@[<hov 2> type (%d) %a @]" (List.length tl) Name.print x
        end
    | FBeginSec n -> 
        if kind = `Coq then fprintf fmt "@[<hov 2>Section %a." Name.print n
    | FEndSec n -> 
        if kind = `Coq then fprintf fmt "@]End %a." Name.print n

  let print_all kind fmt l = print_list newline (print kind) fmt l

end
        
