formula:
  | f1 = formula i = COMBINE f2 = formula 
    { embrace f1.loc f2.loc ( FCombine (f1,f2)) }
  | p = NOT f = aformula { embrace p f.loc (FUnary (Neg, f)) }

nterm:
  | p = LETREGION l = sfunargs IN t = nterm
    { Loc.mk (embrace' p t.loc) (PLetReg (List.map (fun (x,t) -> x.v,t) l,t)) }

decl:
  | USE xl = sfunargs
    { DUse (List.map (fun (x,t) -> x.v, t) xl) }
  | REGION xl = sfunargs
    { DRegion (List.map (fun (x,t) -> x.v, t) xl) }
