%{
  open Loc
  open Const
  open AnnotParseTree

  let mk_term v l = { v = v ; loc = l }
%}

%start <AnnotParseTree.theory> main
%%

main:
  | l = decl* { l }
decl:
  | AXIOM id = defprogvar_no_pos g = gen COLON t = term 
    { Axiom (id,mk_term (Gen (g,t)) t.loc) }

term:
  | c = constant { let p,c = c in mk_term (Const c) p }

