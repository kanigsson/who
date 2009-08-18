funargs : 
  | CAP LPAREN caps = nonempty_list(IDENT) RPAREN l = sfunargs 
    { strip_info caps, l }

formula:
  | f1 = formula i = COMBINE f2 = formula 
    { embrace f1.loc f2.loc ( FCombine (f1,f2)) }
  | p = NOT f = aformula { embrace p f.loc (FUnary (Neg, f)) }

appterm:
  | REF LCURL i = IDENT RCURL t = aterm { Loc.mk t.loc (PRef(i.v,t)) }

nterm:
  | p = LETREGION l = sfunargs IN t = nterm
    { Loc.mk (embrace' p t.loc) (PLetReg (List.map (fun (x,t) -> x.v,t) l,t)) }

decl:
  | USE xl = sfunargs
    { DUse (List.map (fun (x,t) -> x.v, t) xl) }
  | REGION xl = sfunargs
    { DRegion (List.map (fun (x,t) -> x.v, t) xl) }
  | CAP xl = nonempty_list(IDENT) { DCap (strip_info xl) }
