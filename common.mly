%{
  open Loc
  open Const
%}
%%

(* a program variable which can be used in declarations *)
%public defprogvar:
  | x = IDENT { x }
  | x = infix { { c = snd x; info = fst x } }
  | x = prefix { { c = snd x; info = fst x } }
  | p = REF { Loc.mk p "ref" }
  | p = DEXCLAM { Loc.mk p "!!" }
  
%public defprogvar_no_pos : x = defprogvar { x.c }
%public tconstant:
  | BOOL { Const.TBool }
  | TINT { Const.TInt }
  | UNIT { Const.TUnit }
  | PROP { Const.TProp }

%public gen:
  | LBRACKET tl = list(TYVAR) MID rl=list(IDENT) MID el =
    list(TYVAR) RBRACKET 
    { tl, strip_info rl, el }

(* infix operators - can be used in definitions *)
%public %inline infix:
  | p = GT         { p,">" }
  | p = LT         { p,"<" }
  | p = MINUS      { p,"-" }
  | p = PLUS       { p,"+" }
  | p = STAR       { p,"*" }
  | p = ASSIGN     { p,":=" }
  | p = LE         { p,"<=" }
  | p = GE         { p,">=" }
  | p = EQUAL      { p,"=" }
  | p = BEQUAL     { p,"==" }
  | p = BNEQ       { p,"!=" }
  | p = NEQ        { p,"<>" }
  | p = AND        { p,"/\\" }
  | p = OR        { p,"\\/" }
  | p = COMMA      { p,"," }
  | p = ARROW      { p,"->" }
  | p = BLE         { p,"<<=" }
  | p = BGE         { p,">>=" }
  | p = BGT         { p,">>" }
  | p = BLT         { p,"<<" }

(* prefix operators - can be used in definitions *)
%public prefix:
  | p = EXCLAM { p, "!" }
  | p = TILDE { p, "~" }

%public constant:
  | n = INT    { n.info, Const.Int n.c }
  | p = TRUE   { p, Const.Btrue }
  | p = FALSE  { p, Const.Bfalse }
  | p = PTRUE  { p, Const.Ptrue }
  | p = PFALSE { p, Const.Pfalse }
  | p = VOID   { p, Const.Void }

