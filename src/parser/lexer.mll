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

let create_info lexbuf =
  let spos_p = Lexing.lexeme_start_p lexbuf in
  let epos_p = Lexing.lexeme_end_p lexbuf in
    { Loc.st= (spos_p.pos_lnum, spos_p.pos_cnum - spos_p.pos_bol ) ;
      en = (epos_p.pos_lnum, epos_p.pos_cnum - epos_p.pos_bol )}


(* decide if a string is a keyword or an identifier *)
let id_or_keyword =
  let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      [
        ("True", fun i -> PTRUE (create_info i) );
        ("False", fun i -> PFALSE (create_info i) );
        ("let", fun i -> LET (create_info i)  );
        ("axiom", fun i -> AXIOM (create_info i)  );
        ("goal", fun i -> GOAL (create_info i)  );
        ("logic", fun i -> LOGIC (create_info i)  );
        ("parameter", fun i -> PARAMETER (create_info i)  );
        ("type", fun i -> TYPE (create_info i)  );
        ("forall", fun i -> FORALL (create_info i)  );
        ("exists", fun i -> EXISTS (create_info i)  );
        ("for", fun i -> FOR (create_info i)  );
        ("to", fun i -> TO (create_info i)  );
        ("of", fun _ -> OF );
        ("downto", fun i -> DOWNTO (create_info i)  );
        ("do", fun _ -> DO );
        ("done", fun i -> DONE (create_info i)  );
        ("int", fun i -> TINT (create_info i));
        ("prop", fun i -> PROP (create_info i));
        ("begin", fun i -> LPAREN (create_info i));
        ("end", fun i -> RPAREN (create_info i) );
        ("ref", fun i -> REF (create_info i) );
        ("in", fun _ -> IN );
        ("if", fun i -> IF (create_info i) );
        ("letregion", fun i -> LETREGION (create_info i) );
        ("then", fun _ -> THEN );
        ("else", fun _ -> ELSE );
        ("rec", fun _ -> REC );
        ("section", fun i -> SECTION (create_info i) );
        ("coq", fun _ -> COQ );
        ("allocates", fun _ -> ALLOCATES );
        ("predefined", fun _ -> PREDEFINED );
        ("takeover", fun _ -> TAKEOVER );
        ("pangoline", fun _ -> PANGOLINE );
        ("inductive", fun _ -> INDUCTIVE );
        ("end", fun i -> END (create_info i) );
        ("fun", fun i -> FUN (create_info i) );
        ("INTROS", fun _ -> INTROS );
      ];
    fun s -> try Hashtbl.find h s with Not_found ->
      fun i -> IDENT (Loc.mk (create_info i) s)

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
let module_name = alpha_upper (alpha | digit | '\'')*
let name = alpha (alpha | digit | '\'')*
let identifier = (module_name '.')? name

rule token = parse
  | [' ' '\t' ]
      { token lexbuf }
  | digit+ as i
  { INT (Loc.mk (create_info lexbuf) (Big_int.big_int_of_string i)) }
  | identifier as i { id_or_keyword i lexbuf}
  | '"' ( [ ^ '"' ] * as str ) '"'
    { STRING str }
  | '\'' (identifier as tv) { TYVAR (Loc.mk (create_info lexbuf) tv)}
  | "->" { ARROW (create_info lexbuf) }
  | "==" { BEQUAL (create_info lexbuf) }
  | '=' { EQUAL (create_info lexbuf) }
  | "<>" { NEQ (create_info lexbuf) }
  | "()" { VOID (create_info lexbuf)  }
  | '(' { LPAREN (create_info lexbuf)  }
  | ')' { RPAREN (create_info lexbuf)  }
  | '[' { LBRACKET (create_info lexbuf) }
  | ']' { RBRACKET (create_info lexbuf) }
  | '{' { LCURL (create_info lexbuf) }
  | '}' { RCURL (create_info lexbuf) }
  | "{{" { DLCURL }
  | "}}" { DRCURL }
  | "[[" { DLBRACKET (create_info lexbuf) }
  | "]]" { DRBRACKET (create_info lexbuf) }
  | "!!" { DEXCLAM (create_info lexbuf) }
  | "!=" { BNEQ (create_info lexbuf) }
  | '!' { EXCLAM (create_info lexbuf) }
  | ":=" { ASSIGN (create_info lexbuf)   }
  | '|'  { MID }
  | '@'  { AT }
  | ';' { SEMICOLON   }
  | '*' { STAR (create_info lexbuf)  }
  | ':' { COLON }
  | ',' { COMMA (create_info lexbuf) }
  | '.' { DOT }
  | '~' { TILDE (create_info lexbuf) }
  | "<=" { LE (create_info lexbuf)  }
  | "/\\" { AND (create_info lexbuf) }
  | "\\/" { OR (create_info lexbuf) }
  | '<' { LT (create_info lexbuf)  }
  | "<<" { BLT (create_info lexbuf) }
  | ">>" { BGT (create_info lexbuf) }
  | "<<=" { BLE (create_info lexbuf) }
  | ">>=" { BGE (create_info lexbuf) }
  | '>' { GT (create_info lexbuf)  }
  | ">=" { GE (create_info lexbuf)  }
  | '+' { PLUS (create_info lexbuf)  }
  | '-' { MINUS (create_info lexbuf)  }
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
