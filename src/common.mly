%{
  open Loc
  open Const
  open ParseTypes

  let partition_effect l = 
    List.fold_right (fun x (rl,el) ->
      match x with
      | `Rvar r -> r ::rl, el
      | `Effvar e -> rl, e::el) l ([],[])

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
  | TINT { Const.TInt }
  | UNIT { Const.TUnit }
  | PROP { Const.TProp }

%public gen:
  | LBRACKET tl = TYVAR* MID rl=IDENT* MID el = TYVAR* RBRACKET
    { tl, strip_info rl, el }
  | { [], [], [] }

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
  | p = PTRUE  { p, Const.Ptrue }
  | p = PFALSE { p, Const.Pfalse }
  | p = VOID   { p, Const.Void }

takeover:
  | PREDEFINED { Predefined }
  | TAKEOVER { TakeOver }
  | fn = STRING { Include fn }

prover:
  | COQ { `Coq }
  | PANGOLINE { `Pangoline }

%public takeoverdecl:
  | p = prover t = takeover { p, t }

%public inst:
  LBRACKET tl = separated_list(COMMA,ty) MID rl = IDENT*
  MID el = sepeffect* RBRACKET
  { tl, strip_info rl, el }

(* basic types *)
stype:
  | x = tconstant { TConst x }
  | v = TYVAR { TVar v }
  | LPAREN t = ty RPAREN { t }
  | v = IDENT i = inst { TApp (v.c,i)  }
  | v = IDENT { TApp (v.c,([],[],[])) }
  | t = stype v = IDENT {TApp (v.c,([t],[],[])) }
  | LPAREN t = ty COMMA l = separated_list(COMMA,ty) RPAREN v = IDENT
    { TApp(v.c,(t::l,[],[])) }

rvar_or_effectvar:
  | x = IDENT { `Rvar x.c }
  | e = TYVAR { `Effvar e }

sepcreateeffect:
  | LCURL e = createeffect RCURL { e }

createeffect:
  | e = effect cl = maycap 
    { let rl, el = e in rl, el, cl }

maycap:
  | { [] }
  | MID l = IDENT* { strip_info l }

effect: | l = rvar_or_effectvar* {partition_effect l }

%public sepeffect:
  | LCURL e = effect RCURL { e }


(* more complex types *)
%public ty:
  | t = stype { t }
  | t1 = ty ARROW t2 = ty { PureArr (t1, t2) }
  | t1 = ty ARROW e = sepcreateeffect t2 = ty %prec ARROW 
    { let rl,el,cl = e in Arrow (t1,t2,(rl,el),cl) }
  | t1 = ty STAR t2 = ty { Tuple (t1, t2) }
  | LT e = effect GT { Map e }
  | DLBRACKET t = ty DRBRACKET { ToLogic t }
  | REF LPAREN id = IDENT COMMA t = ty  RPAREN { Ref (id.c,t) }

%public maycapdef:
  | {[] }
  | ALLOCATES l = IDENT+ { (strip_info l) }

