%nonassoc forall
%nonassoc let_
%right ARROW
%nonassoc ifprec
%left AND
%nonassoc IN
%nonassoc ASSIGN
%nonassoc LE LT
%right EQUAL NEQ
%right COMBINE
%left PLUS MINUS
%right STAR
%start <Concretesigs.Ptree.prog> main

%%

simple_aftype:
  | tl = tyapplist t2 = IDENT 
    { Loc.mk t2.loc (TApp (t2.v,tl)) }
aftype:
tyapplist: x = parenlist(simple_aftype) { x }

funargs : 
  | CAP LPAREN caps = nonempty_list(IDENT) RPAREN l = sfunargs 
    { strip_info caps, l }
  | l = sfunargs { [], l }

aformula:
  | b = IDENT MID id = IDENT { embrace b.loc id.loc (FLVar (b.v,id.v)) }
  | f1 = aformula MIDCURL e = effect p = RCURL 
    { embrace f1.loc p (FRestrict (e,f1)) }

appformula:
  | f = aformula { f }

formula:
  | f1 = formula i = COMBINE f2 = formula 
    { embrace f1.loc f2.loc ( FCombine (f1,f2)) }
  | p = NOT f = aformula { embrace p f.loc (FUnary (Neg, f)) }
  | f = formbinder(FORALL,DOT) { f }
  | b = FORALL l = list(TYVAR) DOT f = formula  %prec forall
    { embrace b.loc f.loc (FTyGen (strip_info l, f)) }
  | f = formbinder(EXISTS,DOT) { f }

aterm:
  | f = enclosed_dcurl(formula) { Loc.mk f.loc (PPure f) } 
  | l = LPAREN e = nterm COLON t = aftype r =  RPAREN 
    { embrace l r (PAnnot (e,t)) }

appterm:
  | REF LCURL i = IDENT RCURL t = aterm { Loc.mk t.loc (PRef(i.v,t)) }

nterm:
  | p = LETREGION l = sfunargs IN t = nterm
    { Loc.mk (embrace' p t.loc) (PLetReg (List.map (fun (x,t) -> x.v,t) l,t)) }

  | p1 = LET REC id = IDENT gl = genlist 
    idl = funargs COLON ft = aftype EQUAL b = funcbody
    { 
      let p,t,q = b in
      let info = embrace' p1 (opt_info q) in
      let caps, idl = idl in
      match idl with
      | [] -> assert false
      | [x,ty] -> info, Some id.v, gl, Loc.mk info (PRec ([],id.v,ft,x.v,ty,p,t,q))
      | l ->
          let t = makelambda p q ([],(List.tl idl)) t in
          let x,ty = List.hd idl in
          info, Some id.v, gl, 
          Loc.mk info (PRec (caps,id.v,ft,x.v,ty,None,t,PNone))
    }

decl:
  | USE xl = sfunargs
    { DUse (List.map (fun (x,t) -> x.v, t) xl) }
  | REGION xl = sfunargs
    { DRegion (List.map (fun (x,t) -> x.v, t) xl) }
  | CAP xl = nonempty_list(IDENT) { DCap (strip_info xl) }

main: l = nonempty_list(decl) EOF { l }
