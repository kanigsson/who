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
    | Ast.Gen (g,f) -> aux ((Gen g)::acc) f
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
  fprintf fmt "Variables %a :@ %s.@\n" (print_list space Name.print) l s

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
      fprintf fmt "@[Variable %a:@ %a%a.@]" 
      Name.print x pr_generalize g (Ty.print ~print_map:false) t
  | Hypo (h,e) -> 
      fprintf fmt "@[Hypothesis %a:@ %a.@]" 
        Name.print h (Ast.Recon.print ~tyapp:false) e
  | Axiom (x,g,t) -> 
      fprintf fmt "@[Axiom %a: %a %a. @]" Name.print x 
        pr_generalize g (Ast.Recon.print ~tyapp:false) t
  | Type (x,g) -> 
      fprintf fmt "@[Parameter %a :@ %a%s.@]" Name.print x pr_generalize g "Set"

let rec print fmt = function
  | Empty -> ()
  | PO (x,e) -> 
      fprintf fmt "@[Lemma %a:@ %a.@]@." Name.print x 
        (Ast.Recon.print ~tyapp:false) e
  | Section (x,il,sl) -> 
      fprintf fmt "@.@[<hov 2>Section %a.@\n %a@\n %a@.End %a@].@\n"
        Name.print x (print_list fullstop pr_intro) il (print_list break print) sl
        Name.print x

let print_decls fmt () = 
  fprintf fmt "Set Implicit Arguments.@.";
  fprintf fmt "Require Import simple_map.@.";
  fprintf fmt "Open Scope Z_scope.@.";
  fprintf fmt "Require Omega.@.";
  fprintf fmt "Variable ref : forall (a : Set) (k : key), Set.@.";
  fprintf fmt "Definition ___get (A : Set) (k : key) (r : ref A k) (m : kmap) :=
    __get A k m.@.";
  fprintf fmt "Notation \"!!\" := (___get) (at level 50).@."

let print_all fmt s = 
  print_decls fmt ();
  print fmt s

