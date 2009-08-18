{
  open Parser
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
        ("true", fun i -> TRUE (create_info i) );
        ("false", fun i -> FALSE (create_info i) );
        ("True", fun i -> PTRUE (create_info i) );
        ("False", fun i -> PFALSE (create_info i) );
        ("let", fun i -> LET (create_info i)  );
        ("axiom", fun i -> AXIOM (create_info i)  );
        ("logic", fun i -> LOGIC (create_info i)  );
        ("parameter", fun i -> PARAMETER (create_info i)  );
        ("type", fun i -> TYPE (create_info i)  );
        ("forall", fun i -> FORALL (create_info i)  );
        ("exists", fun i -> EXISTS (create_info i)  );
        ("for", fun i -> FOR (create_info i)  );
        ("to", fun i -> TO (create_info i)  );
        ("downto", fun i -> DOWNTO (create_info i)  );
        ("do", fun i -> DO );
        ("done", fun i -> DONE (create_info i)  );
        ("bool", fun i -> BOOL  );
        ("int", fun i -> TINT  );
        ("unit", fun i -> UNIT  );
        ("prop", fun i -> PROP  );
        ("begin", fun i -> BEGIN (create_info i));
        ("end", fun i -> END (create_info i) );
        ("ref", fun i -> REF (create_info i) );
        ("in", fun i -> IN );
        ("if", fun i -> IF (create_info i) );
        ("letregion", fun i -> LETREGION (create_info i) );
        ("then", fun i -> THEN );
        ("else", fun i -> ELSE );
        ("rec", fun i -> REC );
        ("fun", fun i -> FUN (create_info i) );
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
let alpha = ['a' - 'z' 'A'-'Z']
let digit = ['0'-'9']
let identifier = alpha (alpha | digit | '\'' | '_')*
let tyvar = '\'' alpha_lower (alpha | digit | '\'' | '_')*

rule token = parse
  | [' ' '\t' ]
      { token lexbuf }
  | digit+ as i
  { INT (Loc.mk (create_info lexbuf) (int_of_string i)) }
  | identifier as i { id_or_keyword i lexbuf}
  | tyvar as tv { TYVAR tv}
  | "->" { ARROW (create_info lexbuf) }
  | "==" { BEQUAL (create_info lexbuf) }
  | '=' { EQUAL (create_info lexbuf) }
  | "<>" { NEQ (create_info lexbuf) }
  | "()" { VOID (create_info lexbuf)  }
  | '(' { LPAREN (create_info lexbuf)  }
  | ')' { RPAREN (create_info lexbuf)  }
  | '[' { LBRACKET   }
  | ']' { RBRACKET   }
  | '{' { LCURL (create_info lexbuf) }
  | '}' { RCURL   }
  | "{{" { DLCURL }
  | "}}" { DRCURL }
  | "!!" { DEXCLAM (create_info lexbuf) }
  | "!=" { BNEQ (create_info lexbuf) }
  | '!' { EXCLAM (create_info lexbuf) }
  | ":=" { ASSIGN (create_info lexbuf)   }
  | '|' { MID   }
  | '*' { STAR (create_info lexbuf)  }
  | ':' { COLON }
  | ',' { COMMA (create_info lexbuf) }
  | '.' { DOT }
  | "<=" { LE (create_info lexbuf)  }
  | "/\\" { AND (create_info lexbuf) }
  | '<' { LT (create_info lexbuf)  }
  | '>' { GT (create_info lexbuf)  }
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
