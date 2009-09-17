open Name
open Ast

type intro = 
  | Gen of Ty.Generalize.t
  | Variable of Name.t * Ty.Generalize.t * Ty.t
  | Type of Name.t * Ty.Generalize.t
  | Hypo of Name.t * Ast.Recon.t
  | Axiom of Name.t * Ty.Generalize.t *  Ast.Recon.t
type section = 
  | Empty
  | PO of Name.t * Ast.Recon.t
  | Section of Name.t * intro list * section list


let intro_eq f = function
  | Gen _ | Variable _ | Type _  -> false
  | Hypo (_,x) -> equal x f
  | Axiom (_,g,x) when Ty.Generalize.is_empty g -> equal x f
  | Axiom _ -> false

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
        aux ( Variable (x,Ty.Generalize.empty,t) :: acc) f
    | Ast.Gen (g,f) -> 
        if Ty.Generalize.is_empty g then aux acc f
        else aux ((Gen g)::acc) f
    | Let (_,_,{v = Logic _}, ((_,{name = Some 
    ("/\\" | "->" | "=" | "<>" | "fst" | "snd" 
     | "," | "!=" | "!!" | "+" | "-" | "*" | "<" | "<=" | ">" | 
     ">=" | "~" | "==" | "<<" | "<<=" | ">>" | ">>=" |
     "empty" | "combine" | "restrict" )},_) as b)
    ,_) -> 
      let _,f = sopen b in
      aux acc f
    | Let (_,g,{v = Logic t},b,_) ->
        let x, f = sopen b in
        aux (Variable (x,g,t)::acc) f
    | Let (_,g,{v = Ast.Axiom a},b,_) ->
        let x, f = sopen b in
        aux (Axiom (x,g,a)::acc) f
    | TypeDef (g,_,x,e) -> 
        aux (Type (x,g)::acc) e
    | f' -> 
        match destruct_infix' f' with
        | Some ({name = Some "->"},f1,f2) -> 
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
        match destruct_infix' f' with
        | Some ({name = Some "->"},_,_) ->
            begin match section f with
            | Empty -> acc
            | s -> s::acc
            end
        | Some ({name = Some "/\\"},f1,f2) -> aux (aux acc f2) f1
        | _ -> 
            if List.exists (intro_eq f) ctx then acc
            else PO (Name.from_string "goal", f) :: acc
  in
  aux [] f

open Myformat

let lname s fmt l = 
  if l = [] then () else
  fprintf fmt "(%a :@ %s)" (print_list space Name.print) l s

let intro_name s fmt l = 
  if l = [] then () else
  fprintf fmt "Variables %a :@ %s." (print_list space Name.print) l s

let pr_generalize fmt ((tl,rl,el) as g) = 
  if Ty.Generalize.is_empty g then ()
  else
    fprintf fmt "forall@ %a@ %a@ %a,@ "
    (lname "Set") tl (lname "key") rl (lname "kmap") el

let pr_intro fmt = function
  | Gen (tl,rl,el) -> 
      fprintf fmt "%a%a%a"
      (intro_name "Set") tl (intro_name "key") rl (intro_name "kmap") el
  | Variable (x,g,t) -> 
      fprintf fmt "@[<hov 2>Variable %a:@ %a%a. @]" 
      Name.print x pr_generalize g (Ty.print ~print_map:false) t
  | Hypo (h,e) -> 
      fprintf fmt "@[Hypothesis %a:@ %a. @]" 
        Name.print h (Ast.Recon.print ~tyapp:false) e
  | Axiom (x,g,t) -> 
      fprintf fmt "@[Axiom %a: %a %a. @]" Name.print x 
        pr_generalize g (Ast.Recon.print ~tyapp:false) t
  | Type (x,g) -> 
      fprintf fmt "@[Parameter %a :@ %a%s. @]" Name.print x pr_generalize g "Set"

let rec print fmt = function
  | Empty -> ()
  | PO (x,e) -> 
      fprintf fmt "@[Lemma %a:@ %a.@]@," Name.print x 
        (Ast.Recon.print ~tyapp:false) e
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
  fprintf fmt "Variable ref : forall (a : Set) (k : key), Set.@\n";
  fprintf fmt "Definition ___get (A : Set) (k : key) (r : ref A k) (m : kmap) :=
    __get A k m.@\n";
  fprintf fmt "Notation \"!!\" := (___get) (at level 50).@\n"

let print_all fmt s = 
  print_decls fmt ();
  print fmt s;
  pp_print_flush fmt ()

module Flatten = struct

  type t = 
    | FCoqDecl of string
    | FGen of Ty.Generalize.t
    | FVariable of Name.t * Ty.Generalize.t * Ty.t
    | FType of Name.t * Ty.Generalize.t
    | FHypo of Name.t * Ast.Recon.t
    | FAxiom of Name.t * Ty.Generalize.t *  Ast.Recon.t
    | FPO of Name.t * Ast.Recon.t
    | FBeginSec of Name.t
    | FEndSec of Name.t

  let intro = function
    | Gen g -> FGen g
    | Variable (n,g,t) -> FVariable (n,g,t)
    | Type (n,t) -> FType (n,t)
    | Hypo (n,e) -> FHypo (n,e)
    | Axiom (n,g,e) -> FAxiom (n,g,e)

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
    List.map (fun s -> FCoqDecl s)
      [
       "Set Implicit Arguments";
       "Require Import WhoMap";
       "Require Import ZArith";
       "Open Scope Z_scope";
       "Require Omega";
       "Variable ref : forall (a : Set) (k : key), Set";
       "Definition ___get (A : Set) (k : key) (r : ref A k) (m : kmap) :=
        __get A k m";
      "Notation \"!!\" := (___get) (at level 50)"
      ]
  let main s = 
    coqdecls @ section s []

  let print fmt = function
    | FCoqDecl s -> fprintf fmt "%s." s
    | FGen (tl,rl,el) -> 
        fprintf fmt "%a%a%a"
        (intro_name "Set") tl (intro_name "key") rl (intro_name "kmap") el
    | FVariable (x,g,t) -> 
        fprintf fmt "@[<hov 2>Variable %a:@ %a%a. @]" 
        Name.print x pr_generalize g (Ty.print ~print_map:false) t
    | FHypo (h,e) -> 
        fprintf fmt "@[Hypothesis %a:@ %a. @]" 
          Name.print h (Ast.Recon.print ~tyapp:false) e
    | FAxiom (x,g,t) -> 
        fprintf fmt "@[Axiom %a: %a %a. @]" Name.print x 
          pr_generalize g (Ast.Recon.print ~tyapp:false) t
    | FType (x,g) -> 
        fprintf fmt "@[Parameter %a :@ %a%s. @]" Name.print x pr_generalize g "Set"
    | FPO (x,e) -> 
        fprintf fmt "@[Lemma %a:@ %a.@]" Name.print x 
          (Ast.Recon.print ~tyapp:false) e
    | FBeginSec n -> fprintf fmt "@[<hov 2>Section %a." Name.print n
    | FEndSec n -> fprintf fmt "@]End %a." Name.print n

  let force_newline = function
    | FBeginSec _ | FEndSec _ -> true
    | _ -> false

  let id x = 
    let n = 
      match x with
      | FAxiom (n,_,_) | FPO (n,_) | FType (n,_) 
      | FHypo (n,_) | FVariable (n,_,_) | FEndSec n | FBeginSec n -> n
      | FGen g -> Ty.Generalize.get_first g
      | FCoqDecl s -> Name.from_string (String.sub s 0 (String.index s ' ')) in
    let s = sprintf "%a" Name.print n in
    match x with
    | FBeginSec _ -> "begin" ^ s
    | FEndSec _ -> "end" ^ s
    | _ -> s

end
        
