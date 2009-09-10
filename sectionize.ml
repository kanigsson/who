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

let pr_intro fmt = function
  | Gen g -> Ty.Generalize.print fmt g
  | Variable (x,_,t) -> 
      fprintf fmt "@[Variable %a:@ %a.@]@." Name.print x Ty.print t
  | Hypo (h,e) -> 
      fprintf fmt "@[Hypothesis %a:@ %a.@]@." Name.print h Ast.Recon.print e
  | Axiom (x,_,t) -> 
      fprintf fmt "@[Axiom %a: %a. @]@." Name.print x Ast.Recon.print t
  | Type (x,_) -> 
      fprintf fmt "@[Parameter %a@ %s.@]@." Name.print x "Set"

let rec print fmt = function
  | Empty -> ()
  | PO (x,e) -> fprintf fmt "@[Lemma %a:@ %a.@]@." Name.print x Ast.Recon.print e
  | Section (x,il,sl) -> 
      fprintf fmt "@[Section %a.@, %a@, %a@]@, End %a.@."
        Name.print x (print_list break pr_intro) il (print_list break print) sl
        Name.print x

