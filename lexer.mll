{
  open Parser
  open Lexing

  exception Error of string

(* decide if a string is a keyword or an identifier *)
let id_or_keyword = 
  let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      [ ("true", TRUE );
        ("false", FALSE );
        ("let", LET  );
        ("bool", BOOL  );
        ("int", TINT  );
        ("unit", UNIT  );
        ("ref", REF  );
        ("in", IN );
        ("fun", FUN );
      ];
    fun s -> try Hashtbl.find h s with Not_found -> IDENT s

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
  { INT (int_of_string i) }
  | identifier as i { id_or_keyword i}
  | tyvar as tv { TYVAR tv}
  | "->" { ARROW }
  | '=' { EQUAL }
  | "<>" { NEQ }
  | "()" { VOID  }
  | '(' { LPAREN   }
  | ')' { RPAREN   }
  | '[' { LBRACKET   }
  | ']' { RBRACKET   }
  | '{' { LCURL   }
  | '}' { RCURL   }
  | '!' { EXCLAM   }
  | ":=" { ASSIGN   }
  | '|' { MID   }
  | '*' { STAR  }
  | ':' { COLON }
  | ',' { COMMA }
  | "<=" { LE  }
  | '<' { LT  }
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
