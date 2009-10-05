
(* ocaml/who preprocessor *)

{
  open Lexing 
  open Format

  let tab_size = 8

  let count_spaces s =
    let c = ref 0 in
    for i = 0 to String.length s - 1 do
      c := !c + (
	if s.[i] = '\t' then
	  tab_size - (!c mod tab_size)
	else
	  1
      )
    done;
    !c

  let make_table l =
    let h = Hashtbl.create 97 in 
    List.iter (fun s -> Hashtbl.add h s ()) l;
    Hashtbl.mem h

  let is_ocaml_keyword = make_table
    [ "and"; "as"; "assert"; "asr"; "begin";
      "class"; "constraint"; "do"; "done"; "downto"; "else"; "end";
      "exception"; "external"; "false"; "for"; "fun"; "function";
      "functor"; "if"; "in"; "include"; "inherit"; "initializer";
      "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match";
      "method"; "mod"; "module"; "mutable"; "new"; "object"; "of";
      "open"; "or"; "private"; "rec"; "sig"; "struct"; "then"; "to";
      "true"; "try"; "type"; "val"; "virtual"; "when"; "while"; "with";
    ] 

  let is_who_keyword = is_ocaml_keyword

  let indentation n =
    let space = 0.5 *. (float n) in
    printf "\n\\noindent\\hspace*{%2.2fem}" space

  let print_ident =
    let char = function
      | '_' -> printf "\\_{}"
      | c -> printf "%c" c
    in
    String.iter char

  let color = false
  let is_tt = ref true
  let vspacing = "\\smallskip"
  let lines = ref false
  let line_number = ref 0
  let add_line_number () =
    if !lines then begin
      incr line_number;
      let space = if !line_number < 10 then "\\phantom{0}" else "" in
      printf "{\\small %s%d}" space !line_number;
    end
}

let space = [' ' '\t' '\r']
let newline = '\n'
let latex_symbol = 
  '\\' | '#' | '$' | ':' | '_' | '%' | '~' | ';' | '&' | '^' 
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '-' '\'']* 
let anychar = ([ ^ 't'] | [ 't'])

rule pp = parse
  | "\\begin{ocaml}" space* '\n'?
      { printf "\n\n%s\\noindent{\\tt\\parindent 0pt\n" vspacing;
	start_of_line lexbuf; ocaml lexbuf; 
	printf "}\n\n%s\\noindent\n" vspacing;
	pp lexbuf }
  | "\\begin{who}" ("[lines]"? as o) space* '\n'?
      { printf "\n\n%s\\noindent{\\tt\\parindent 0pt\n" vspacing;
	lines := o <> ""; line_number := 0;
	add_line_number ();
	start_of_line lexbuf; who lexbuf; 
	printf "}\n\n%s\\noindent\n" vspacing;
	pp lexbuf }
  | eof 
      { () }
  | _ as c
      { printf "%c" c; pp lexbuf }

and ocaml = parse
  | '\n'? space* "\\end{ocaml}" space* '\n'?
      { () }
  | latex_symbol as c 
         { printf "\\symbol{%d}" (Char.code c); ocaml lexbuf }
  | ' '  { printf "\\hspace*{1.22ex}"; ocaml lexbuf }
  | '{'  { if !is_tt then printf "\\symbol{123}" else printf "\\{"; 
	   ocaml lexbuf }
  | '}'  { if !is_tt then printf "\\symbol{125}" else printf "\\}"; 
	   ocaml lexbuf }
  | "->" { printf "\\ensuremath{\\rightarrow}"; ocaml lexbuf }
  | "<-" { printf "\\ensuremath{\\leftarrow}"; ocaml lexbuf }
  | ">"  { printf "\\ensuremath{>}"; ocaml lexbuf }
  | "<"  { printf "\\ensuremath{<}"; ocaml lexbuf }
  | ">=" { printf "\\ensuremath{\\ge}"; ocaml lexbuf }
  | "<=" { printf "\\ensuremath{\\le}"; ocaml lexbuf }
  | "&&" { printf "\\ensuremath{\\land}"; ocaml lexbuf }
  | "|"  { printf "\\ensuremath{|}"; ocaml lexbuf }
  | "||" { printf "\\ensuremath{\\lor}"; ocaml lexbuf }
  | "==" { printf "\\ensuremath{\\equiv}"; ocaml lexbuf }
  | ":=" { printf "\\ensuremath{:=}"; ocaml lexbuf }
  | "!=" { printf "\\ensuremath{\\not\\equiv}"; ocaml lexbuf }
  | "<>" { printf "\\ensuremath{\\not=}"; ocaml lexbuf }
  | "'a" { printf "\\ensuremath{\\alpha}"; ocaml lexbuf }
  | "'a'" as s { printf "%s" s; ocaml lexbuf }
  | "'b" { printf "\\ensuremath{\\beta}"; ocaml lexbuf }
  | "'b'" as s { printf "%s" s; ocaml lexbuf }
  | "*"  { printf "\\ensuremath{\\times}"; ocaml lexbuf }
  | "(*" 
      { 
	printf "{";
	if color then printf "\\color{red}";
	printf "(*"; comment lexbuf; 
	printf "}";
	ocaml lexbuf 
      }
  | ident as s
      { 
	if is_ocaml_keyword s then begin
	  if color then printf "{\\color{blue}"
	  else printf "\\textbf{";
	  printf "%s" s;
	  printf "}"
	end else 
          print_ident s;
	ocaml lexbuf 
      }
  | "\n" 
      { printf "~\\linebreak"; start_of_line lexbuf; ocaml lexbuf }
  | eof  
      { () }
  | _ as c  
      { printf "%c" c; ocaml lexbuf }

and comment = parse
  | "(*" as s 
      { printf "%s" s; comment lexbuf; comment lexbuf }
  | "*)" as s
      { printf "%s" s }
  | latex_symbol as c 
      { printf "\\symbol{%d}" (Char.code c); comment lexbuf }
  | ' '  
      { printf "\\hspace*{1.22ex}"; comment lexbuf }
  | '{'  { if !is_tt then printf "\\symbol{123}" else printf "\\{"; 
	   comment lexbuf }
  | '}'  { if !is_tt then printf "\\symbol{125}" else printf "\\}"; 
	   comment lexbuf }
  | ">" 
      { printf "\\ensuremath{>}"; comment lexbuf }
  | "<" 
      { printf "\\ensuremath{<}"; comment lexbuf }
  | eof  
      { () }
  | _ as c  
      { printf "%c" c; comment lexbuf }

and start_of_line = parse
  | space* as s
      { indentation (count_spaces s) }
  | eof 
      { () }

and who = parse
  | '\n'? space* "\\end{who}" space* '\n'?
      { () }
  | latex_symbol as c 
         { printf "\\symbol{%d}" (Char.code c); who lexbuf }
  | ' '  { printf "\\hspace*{1.22ex}"; who lexbuf }
  | '{'  { if !is_tt then printf "\\symbol{123}" else printf "\\{"; 
	   who lexbuf }
  | '}'  { if !is_tt then printf "\\symbol{125}" else printf "\\}"; 
	   who lexbuf }
  | "->" { printf "\\ensuremath{\\rightarrow}"; who lexbuf }
  | "->" '{' '}'
    { printf "\\ensuremath{\\rightarrow^{\\emptyset}}" ; who lexbuf }
  | "->" '{' ([^'{' '}']+ as contents) '}'
  { printf "\\ensuremath{\\rightarrow^{\\mbox{\\scriptsize\\{%s\\}}}}" contents; who lexbuf }
  | "<-" { printf "\\ensuremath{\\leftarrow}"; who lexbuf }
  | ">"  { printf "\\ensuremath{\\rangle}"; who lexbuf }
  | "<"  { printf "\\ensuremath{\\langle}"; who lexbuf }
  | "< "  { printf "\\ensuremath{<} "; who lexbuf }
  | " >"  { printf " \\ensuremath{>}"; who lexbuf }
  | ">=" { printf "\\ensuremath{\\ge}"; who lexbuf }
  | "<=" { printf "\\ensuremath{\\le}"; who lexbuf }
  | "&&" { printf "\\ensuremath{\\land}"; who lexbuf }
  | "ref(" ( [^ ')']* as i) ")"
    {printf "ref\\ensuremath{_{%s}}" i; who lexbuf }
  | "|"  { printf "\\ensuremath{|}"; who lexbuf }
  | "|" (ident as i)  
  { printf "\\ensuremath{{}_{\\mbox{\\scriptsize|%s}}}" i; who lexbuf }
  | "||" { printf "\\ensuremath{\\lor}"; who lexbuf }
  | "==" { printf "\\ensuremath{\\equiv}"; who lexbuf }
  | ":=" { printf "\\ensuremath{:=}"; who lexbuf }
  | "!=" { printf "\\ensuremath{\\not\\equiv}"; who lexbuf }
  | "<>" { printf "\\ensuremath{\\not=}"; who lexbuf }
  | "/\\" { printf "\\ensuremath{\\land}"; who lexbuf }
  | "forall" space* { printf "\\ensuremath{\\forall}"; who lexbuf }
  | "'a" { printf "\\ensuremath{\\alpha}"; who lexbuf }
  | "'a'" as s { printf "%s" s; who lexbuf }
  | "'b" { printf "\\ensuremath{\\beta}"; who lexbuf }
  | "'b'" as s { printf "%s" s; who lexbuf }
  | "*"  { printf "\\ensuremath{\\times}"; who lexbuf }
  | "[[" {printf "\\ensuremath{\\lceil}"; who lexbuf}
  | "]]" {printf "\\ensuremath{\\rceil}"; who lexbuf}
  | "{{{" (( [^ '}'] | anychar [^ '}'] | anychar anychar [^ '}'])* as t) "}}}"
    { printf "%s" t; who lexbuf }
  | "(*" 
      { 
	printf "{";
	if color then printf "\\color{red}";
	printf "(*"; comment lexbuf; 
	printf "}";
	who lexbuf 
      }
  | ident as s
      { 
	if is_who_keyword s then begin
	  if color then printf "{\\color{blue}"
	  else printf "\\textbf{";
	  printf "%s" s;
	  printf "}"
	end else 
          print_ident s;
	who lexbuf 
      }
  | "\n" 
      { printf "~\\linebreak"; 
	add_line_number ();
	start_of_line lexbuf; who lexbuf }
  | eof  
      { () }
  | _ as c  
      { printf "%c" c; who lexbuf }


{

  let lb = from_channel stdin 
  let () = pp lb; printf "@."

}
