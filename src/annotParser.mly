%{
  open Loc
  open Const
  open AnnotParseTree
  (** TODO compute the type of a recursive function by the given return type and
   * the argument types *)

%}

%start <AnnotParseTree.theory> main
%%

main:
  | l = decl* EOF { l }
decl:
  | AXIOM id = defprogvar_no_pos g = gen COLON t = nterm 
    { Axiom (id,mk_term (Gen (g,t)) t.loc) }
  | GOAL id = defprogvar_no_pos g = gen COLON t = nterm 
    { Goal (id,mk_term (Gen (g,t)) t.loc) }
  | LETREGION l = IDENT* 
    { DLetReg (strip_info l) }
  | SECTION x = IDENT fn = takeoverdecl* l = decl+ END
    { Section (x.c,fn,l) }
  | LOGIC x = defprogvar_no_pos g = gen COLON t = ty
    { Logic (x, g, t) }
  | TYPE x = IDENT g = gen
    { TypeDef (g,None, x.c ) }
  | TYPE x = IDENT g = gen EQUAL t = ty
    { TypeDef (g, Some t, x.c ) }
  | LET x = defprogvar_no_pos g = gen EQUAL t = nterm
    { Program (x,g,t, NoRec) }
  | LET REC x = defprogvar_no_pos g = gen COLON t = ty EQUAL e = nterm
    { Program (x,g,e,Rec t) }
  | LET LOGIC x = defprogvar_no_pos g = gen EQUAL t = nterm
    { Program (x,g,t,LogicDef) }

one_binding:
  LPAREN x = IDENT COLON t = ty RPAREN
  { x.c, t }

term:
  | x = IDENT { svar x.c x.info }
  | x = IDENT i = inst { var x.c i x.info }
  | x = prefix i = inst { let p, s = x in var s i p }
  | x = prefix { let p, s = x in var s Inst.empty p }
  | p = REF i = inst { var "ref" i p}
  | p = DEXCLAM i = inst x = IDENT t = term
    { app (app (var "!!" i p) (svar x.c x.info) (embrace p x.info)) 
        t (embrace p t.loc) }
  | c = constant { let p,c = c in mk_term (Const c) p }
  | p1 = LPAREN t = nterm p2 = RPAREN 
    { mk_term t.v (embrace p1 p2) }
  | p1 = LPAREN i = infix inst = inst p2 = RPAREN
    { let _,x = i in mk_term (Var (x,inst)) (embrace p1 p2) }
  | l = LPAREN e = nterm COLON t = ty r = RPAREN 
    { mk_term (Annot (e,t)) (embrace l r) }

appterm:
  | t = term { t }
  | t1 = appterm t2 = term 
    { app t1 t2 (embrace t1.loc t2.loc) }
  | t1 = appterm DLCURL l = IDENT* DRCURL t2 = term 
    {app ~cap:(strip_info l) t1 t2 (embrace t1.loc t2.loc) }

nterm:
  | t = appterm { t }
  | t1 = nterm i = infix t2 = nterm  
    { appi (snd i) t1 t2 (embrace t1.loc t2.loc) }
  | t1 = nterm i = infix inst = inst t2 = nterm  
    { appi ~inst (snd i) t1 t2 (embrace t1.loc t2.loc) }
  | sp = FORALL l = one_binding DOT e = nterm %prec forall
    { let x,t = l in mk_term (Quant (`FA,t,x,e)) (embrace sp e.loc) }
  | sp = FORALL g = gen DOT e = nterm %prec forall
    { mk_term (Gen (g,e)) (embrace sp e.loc) }
  | sp = EXISTS l = one_binding DOT e = nterm %prec forall
    { let x,t = l in mk_term (Quant (`EX,t,x,e)) (embrace sp e.loc) }
  | sp = FUN l = one_binding ARROW e = nterm 
    { let x,t = l in mk_term (PureFun (t,x,e)) (embrace sp e.loc) }
  | sp = FUN l = one_binding ARROW body = funcbody
    { let cap, p,e,q = body in
      let x,t = l in
      mk_term (Lam (x,t,cap,p,e,q)) (embrace sp q.loc) 
    }
  | st = IF it = nterm THEN tb = nterm ELSE eb = nterm %prec ifprec
    { mk_term (Ite(it,tb,eb)) (embrace st eb.loc) }
  | st = LET x = defprogvar_no_pos g = gen EQUAL t1 = nterm IN t2 = nterm %prec let_
    { mk_term (Let (g,t1,x,t2, NoRec)) (embrace st t2.loc) }
  | st = LET LOGIC x = defprogvar_no_pos g = gen EQUAL t1 = nterm 
     IN t2 = nterm %prec let_
    { mk_term (Let (g,t1,x,t2, LogicDef)) (embrace st t2.loc) }
  | st = LET REC x = defprogvar_no_pos g = gen COLON t = ty 
    EQUAL t1 = nterm IN t2 = nterm %prec let_
    { mk_term (Let (g,t1,x,t2, Rec t)) (embrace st t2.loc) }
  | p = LETREGION l = IDENT* IN t = nterm %prec let_
    { mk_term (LetReg (strip_info l,t)) (embrace p t.loc) }
  | p = PARAMETER LPAREN t = ty COMMA e = sepeffect r = RPAREN
    { mk_term (Param (t,e)) (embrace p r) }
  | l = DLBRACKET p = nterm DRBRACKET e = nterm DLBRACKET q = nterm r = DRBRACKET
    { mk_term (HoareTriple (p,e,q)) (embrace l r) }
    

funcbody:
  cap = maycapdef p = spec e = nterm q = spec { cap, p,e,q }

spec:
  LCURL t = nterm RCURL { t }
