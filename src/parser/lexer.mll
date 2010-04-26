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

{
  open Tokens
  open Lexing

  exception Error of string

(* decide if a string is a keyword or an identifier *)
let id_or_keyword =
  let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      [
        ("let", LET );
        ("axiom", AXIOM  );
        ("goal",  GOAL  );
        ("lemma",  LEMMA  );
        ("logic",  LOGIC  );
        ("parameter",  PARAMETER  );
        ("type",  TYPE );
        ("forall",  FORALL   );
        ("exists",  EXISTS  );
        ("for",  FOR );
        ("to",  TO );
        ("of",  OF );
        ("downto",  DOWNTO );
        ("do",  DO );
        ("done",  DONE );
        ("int",  TINT );
        ("prop",  PROP );
        ("begin",  BEGIN );
        ("end",  END );
        ("ref",  REF );
        ("match",  MATCH );
        ("with",  WITH );
        ("in",  IN );
        ("if",  IF );
        ("letregion",  LETREGION );
        ("then",  THEN );
        ("else",  ELSE );
        ("rec",  REC );
        ("section",  SECTION );
        ("coq",  COQ );
        ("predefined",  PREDEFINED );
        ("takeover",  TAKEOVER );
        ("pangoline",  PANGOLINE );
        ("inductive",  INDUCTIVE );
        ("fixpoint",  FIXPOINT );
        ("fun",  FUN );
      ];
    fun s -> try Hashtbl.find h s with Not_found -> IDENT s

let constructor_or_keyword =
  let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      [
        ("True",  PTRUE );
        ("False", PFALSE  );
      ];
    fun s -> try Hashtbl.find h s with Not_found -> CONSTRUCTOR s

let incr_linenum lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
       { pos with
        pos_lnum = pos.pos_lnum + 1;
        pos_bol = pos.pos_cnum;
        }

}

let alpha_lower = ['a'-'z' ]
let alpha_upper = ['A'-'Z']
let alpha = ['a' - 'z' 'A'-'Z' '_' ]
let digit = ['0'-'9']
let module_or_constructor_name = alpha_upper (alpha | digit | '\'')*
let name = alpha_lower (alpha | digit | '\'')*
let identifier = (module_or_constructor_name '.')* name

rule token = parse
  | [' ' '\t' ]
      { token lexbuf }
  | '_' { UNDERSCORE }
  | digit+ as i { INT (Big_int.big_int_of_string i) }
  | identifier as i { id_or_keyword i }
  | module_or_constructor_name as m { constructor_or_keyword m }
  | '"' ( [ ^ '"' ] * as str ) '"'
      { STRING str }
  | '\'' (name as tv) { TYVAR tv}
  | "->" { ARROW }
  | "==" { BEQUAL }
  | '=' { EQUAL }
  | "<>" { NEQ }
  | "()" { VOID }
  | '(' { LPAREN }
  | ')' { RPAREN  }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '{' { LCURL }
  | '}' { RCURL }
  | "[[" { DLBRACKET }
  | "]]" { DRBRACKET }
  | "!!" { DEXCLAM }
  | "!=" { BNEQ }
  | '!' { EXCLAM }
  | ":=" { ASSIGN }
  | '|'  { MID }
  | '@'  { AT }
  | ';' { SEMICOLON   }
  | '*' { STAR  }
  | ':' { COLON }
  | ',' { COMMA }
  | '.' { DOT }
  | '~' { TILDE }
  | "<=" { LE  }
  | "/\\" { AND }
  | "\\/" { OR }
  | '<' { LT  }
  | "<<" { BLT }
  | ">>" { BGT }
  | "<<=" { BLE }
  | ">>=" { BGE }
  | '>' { GT  }
  | ">=" { GE  }
  | '+' { PLUS }
  | '-' { MINUS }
  | "(*" { comment lexbuf; token lexbuf }
  | eof { EOF  }
  | '\n' { incr_linenum lexbuf ; token lexbuf }
  | _
      { raise (Error (Lexing.lexeme lexbuf)) }

and comment = parse
  | "(*" { comment lexbuf; comment lexbuf}
  | '\n' { incr_linenum lexbuf ; comment lexbuf }
  | "*)" { () }
  | eof { raise (Error "unterminated comment") }
  | _ { comment lexbuf }

{
  let reset lexbuf =
    lexbuf.lex_curr_p <-
       { lexbuf.lex_curr_p with pos_lnum = 1; pos_bol = 0; }
}
