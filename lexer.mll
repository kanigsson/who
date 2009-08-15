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
        ("axiom", fun i -> LOGIC (create_info i)  );
        ("logic", fun i -> AXIOM (create_info i)  );
        ("type", fun i -> TYPE (create_info i)  );
        ("bool", fun i -> BOOL  );
        ("int", fun i -> TINT  );
        ("unit", fun i -> UNIT  );
        ("prop", fun i -> PROP  );
        ("ref", fun i -> REF  );
        ("in", fun i -> IN );
        ("if", fun i -> IF (create_info i) );
        ("then", fun i -> THEN );
        ("else", fun i -> ELSE );
        ("fun", fun i -> FUN (create_info i) );
      ];
    fun s -> try Hashtbl.find h s with Not_found -> 
      fun i -> IDENT (Loc.mk (create_info i) s)

let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- 
       { pos with
        Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
        Lexing.pos_bol = pos.Lexing.pos_cnum;
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
  | "->" { ARROW }
  | '=' { EQUAL }
  | "<>" { NEQ }
  | "()" { VOID (create_info lexbuf)  }
  | '(' { LPAREN (create_info lexbuf)  }
  | ')' { RPAREN (create_info lexbuf)  }
  | '[' { LBRACKET   }
  | ']' { RBRACKET   }
  | '{' { LCURL (create_info lexbuf) }
  | '}' { RCURL   }
  | '!' { EXCLAM (create_info lexbuf) }
  | ":=" { ASSIGN   }
  | '|' { MID   }
  | '*' { STAR  }
  | ':' { COLON }
  | ',' { COMMA }
  | "<=" { LE  }
  | "/\\" { AND }
  | '<' { LT  }
  | '>' { GT  }
  | '+' { PLUS  }
  | '-' { MINUS  }
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
