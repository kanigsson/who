%{
  open Loc
  open Const
  open AnnotParseTree

  let mk_term v l = { v = v ; loc = l }
%}

%start <AnnotParseTree.theory> main
%%

main:
  | l = decl* EOF { l }
decl:
  | AXIOM id = defprogvar_no_pos g = gen COLON t = term 
    { Axiom (id,mk_term (Gen (g,t)) t.loc) }
  | REGION l = IDENT* 
    { LetReg (strip_info l) }
  | SECTION x = IDENT fn = takeoverdecl* l = decl+ END
    { Section (x.c,fn,l) }
  | LOGIC x = defprogvar_no_pos g = gen COLON t = ty
    { Logic (x, g, t) }
  | TYPE x = IDENT g = gen
    { TypeDef (g,None, x.c ) }
  | TYPE x = IDENT g = gen EQUAL t = ty
    { TypeDef (g, Some t, x.c ) }

term:
  | c = constant { let p,c = c in mk_term (Const c) p }

