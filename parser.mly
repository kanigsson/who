%{
  open Loc
  open Ast
  open ParseT
  module SS = Misc.SS

  let list_to_set x = 
    List.fold_left (fun acc x -> SS.add x acc) SS.empty x

  let rec merge = function
    | [] -> const Const.Void Loc.dummy
    | { v = Let (l,t,x,{ v = Const Const.Void },r); loc = loc }::xs -> 
        let_ l t x (merge xs) r loc
    | { v = TypeDef (l,t,x,{ v = Const Const.Void }); loc = loc }::xs -> 
        typedef l t x (merge xs) loc
    | _ -> assert false

  let embrace inf1 inf2 = { st = inf1.st ; en = inf2.en }

  let mk_lam f l loc =
    let l = List.rev l in
    match l with
    | [] -> assert false
    | (x,t)::xs ->
        let acc = f x t loc in
        List.fold_left (fun acc (x,t) -> pure_lam x t acc loc) acc xs
        
  let mk_pure_lam l e = mk_lam (fun x t -> pure_lam x t e) l 
  let mk_efflam l p e q = mk_lam (fun x t -> lam x t p e q) l
  let mk_param l p q rt eff loc = 
    mk_efflam l p (mk (Param (rt,eff)) loc) q loc

  let mk_quant k l e loc = 
    List.fold_right (fun (x,t) acc -> quant k x t acc loc) l e

  let let_wconst l t x r p = let_ l t x (const (Const.Void) p) r p

  let forfunction dir i start end_ inv body pos =
    let forterm = mk (For (dir,inv,i.c,body)) pos in
    let em = Ty.Generalize.empty in
    (* let start = start and end_ = end_ in 
       forvar inv start end_ body *)
    let_ em start "%%start" (let_ em end_ "%%end_" forterm NoRec end_.loc) 
      NoRec start.loc



%}

%token <int Loc.t> INT
%token <Loc.loc> LPAREN RPAREN LCURL BEGIN END
%token LBRACKET RBRACKET RCURL DLCURL DRCURL
%token <string Loc.t> IDENT
%token <string> TYVAR
%token IN 
%token <Loc.loc> PLUS MINUS EQUAL STAR NEQ BEQUAL BNEQ ARROW COMMA AND
%token <Loc.loc> ASSIGN GE GT LE LT REF LETREGION
%token EOF
%token REC
%token <Loc.loc> EXCLAM DEXCLAM IF FUN TRUE FALSE PTRUE PFALSE VOID LET AXIOM
%token <Loc.loc> LOGIC TYPE FORALL EXISTS PARAMETER TO DOWNTO FOR DONE
%token COLON MID THEN ELSE   BOOL TINT UNIT PROP DOT DO

%nonassoc forall
%nonassoc let_
%right ARROW
%nonassoc ifprec
%left AND
%nonassoc LE LT GE GT
%nonassoc ASSIGN
%right EQUAL NEQ BEQUAL BNEQ
%right COMMA
%left PLUS MINUS
%right STAR

%start <Ast.ParseT.t> main
%%

progvar: 
  | x = IDENT { x }

defprogvar:
  | x = progvar { x }
  | x = infix { { c = snd x; info = fst x } }
  | x = prefix { { c = snd x; info = fst x } }
  | p = DEXCLAM { Loc.mk p "!!" }
  
rvar: x = IDENT { x }
effvar : x = IDENT { x }

progvar_no_pos: x = progvar { x.c }
defprogvar_no_pos : x = defprogvar { x.c }
rvar_no_pos : x = rvar { x.c }
effvar_no_pos : x = effvar { x.c }
tconstant:
  | BOOL { Const.TBool }
  | TINT { Const.TInt }
  | UNIT { Const.TUnit }
  | PROP { Const.TProp }

stype:
  | x = tconstant { Ty.const x }
  | v = TYVAR { Ty.var v }
  | LPAREN t = ty RPAREN { t }
  | v = IDENT i = inst { Ty.app v.c i }

effect:
  | lr = list(rvar_no_pos) MID le =  list(effvar_no_pos) cl = maycap
    { list_to_set lr, list_to_set le, list_to_set cl}

sepeffect:
  | LCURL e = effect RCURL { e }

ty:
  | t = stype { t }
  | t1 = ty ARROW t2 = ty { Ty.parr t1 t2 }
  | t1 = ty ARROW e = sepeffect t2 = ty %prec ARROW 
    { Ty.arrow t1 t2 e }
  | t1 = ty STAR t2 = ty { Ty.tuple t1 t2 }
  | LT e = effect GT { Ty.map e }
  | REF LPAREN id = rvar_no_pos COMMA t = ty  RPAREN { Ty.ref_ id t }

inst:
  LBRACKET tl = list(ty) MID rl = list(rvar_no_pos) MID el = list(sepeffect) RBRACKET
  { tl, rl, el }

maycap:
  | { [] }
  | MID l = list(rvar_no_pos) { l }

constant:
  |  n = INT    { n.info, Const.Int n.c }
  |  p = TRUE   { p, Const.Btrue }
  |  p = FALSE  { p, Const.Bfalse }
  |  p = PTRUE  { p, Const.Ptrue }
  |  p = PFALSE { p, Const.Pfalse }
  |  p = VOID   { p, Const.Void }

%inline infix:
  | p = MINUS      { p,"-" }
  | p = PLUS       { p,"+" }
  | p = STAR       { p,"*" }
  | p = ASSIGN     { p,":=" }
  | p = LT         { p,"<" }
  | p = LE         { p,"<=" }
  | p = GT         { p,">" }
  | p = GE         { p,">=" }
  | p = EQUAL      { p,"=" }
  | p = BEQUAL     { p,"==" }
  | p = BNEQ       { p,"!=" }
  | p = NEQ        { p,"<>" }
  | p = AND        { p,"/\\" }
  | p = COMMA      { p,"," }
  | p = ARROW      { p,"->" }

%inline infix_nopos:
  | x = infix { snd x }

%inline prefix:
  | p = EXCLAM { p, "!" }
  | p = REF { p, "ref" }

aterm:
  | x = progvar { var x.c x.info }
  | x = prefix { var (snd x) (fst x) }
  | c = constant { let p,c = c in const c p }
  | l = LPAREN x = infix_nopos e = RPAREN { var x (embrace l e) }
  | l = LPAREN t = nterm e = RPAREN { mk t.v (embrace l e) }
  | l = BEGIN t = nterm e = END { mk t.v (embrace l e) }
  | l = LPAREN e = nterm COLON t = ty r = RPAREN { mk (Annot (e,t)) (embrace l r) }

appterm:
  | t = aterm { t }
  | t1 = appterm DLCURL l = list(rvar_no_pos) DRCURL t2 = aterm 
    {cap_app t1 t2 l (embrace t1.loc t2.loc) }
  | t1 = appterm t2 = aterm { app t1 t2 (embrace t1.loc t2.loc) }

nterm:
  | p = DEXCLAM x = progvar 
    { app2 "!!" (var x.c x.info) (var "cur" p) (embrace p x.info) }
  | p = DEXCLAM x = progvar MID t = aterm 
    { app2 "!!" (var x.c x.info) t (embrace p t.loc)  }
  | t1 = appterm { t1 }
  | t1 = nterm i = infix_nopos t2 = nterm  
    { appi i t1 t2 (embrace t1.loc t2.loc) }
  | sp = FUN l = arglist ARROW body = funcbody
    { let p,e,q = body in
      mk_efflam l (snd p) e (snd q) (embrace sp (fst q)) }
  | sp = FUN l = arglist ARROW e = nterm 
    { mk_pure_lam l e (embrace sp e.loc) }
  | sp = FORALL l = arglist DOT e = nterm %prec forall
    { mk_quant FA l e (embrace sp e.loc) }
  | sp = EXISTS l = arglist DOT e = nterm %prec forall
    { mk_quant EX l e (embrace sp e.loc) }
  | b = letwithoutargs EQUAL t = nterm IN t2 = nterm %prec let_
    { let p,x,l = b in
      let_ l t x t2 NoRec p}
  | b = letwithargs EQUAL body = funcbody IN t2 = nterm %prec let_
    { let p,x,l,args = b in
      let pre,e,q = body in
      let_ l (mk_efflam args (snd pre) e (snd q) p) x t2 NoRec (embrace p t2.loc) }
  | b = letwithargs EQUAL t1 = nterm IN t2 = nterm %prec let_
    { let p,x,l,args = b in
      let_ l (mk_pure_lam args t1 p) x t2 NoRec (embrace p t2.loc) }
  | p = LETREGION l = list(rvar_no_pos) IN t = nterm %prec let_
    { mk (LetReg (l,t)) p }
  | st = IF it = nterm THEN tb = nterm ELSE eb = nterm %prec ifprec
    { mk (Ite(it,tb,eb)) (embrace st eb.loc) }
  | f = letrec IN e2 = nterm %prec let_ { (f : ParseT.t -> ParseT.t) e2 }
  | st = FOR i = progvar EQUAL e1 = nterm dir = todownto e2 = nterm DO 
       p = precond
       e3 = nterm 
    en = DONE
    { forfunction dir i e1 e2 (snd p) e3 (embrace st en) }

todownto:
  | TO { "forto" }
  | DOWNTO { "fordownto" }

onetyarg:
  LPAREN xl = nonempty_list(defprogvar_no_pos) COLON t = ty RPAREN
    { List.map (fun x -> x,t) xl }

arglist: l = nonempty_list(onetyarg) { List.flatten l }

letwithargs:
  | p = LET x = defprogvar_no_pos l = optgen args = arglist
  { p, x, l, args }

letwithoutargs:
  | p = LET x = defprogvar_no_pos l = optgen 
    { p,x,l }

letrec:
  | p = LET REC l = optgen LPAREN x = defprogvar_no_pos 
    COLON t = ty RPAREN args = arglist EQUAL b = funcbody
    { let pre,e,q = b in
      (fun e2 -> let_ l (mk_efflam args (snd pre) e (snd q) p) x e2 (Rec t)
        (embrace p e2.loc))
    }
    

funcbody:
  p = precond e = nterm q = postcond { p,e,q }

postcond:
  | p = LCURL RCURL { p, PNone }
  | p = LCURL t = nterm RCURL { p, PPlain t}
  | p = LCURL x = defprogvar_no_pos COLON t = nterm RCURL { p, PResult (x,t)}

precond:
  | p = LCURL RCURL { p, None }
  | p = LCURL t = nterm RCURL { p, Some t}

optgen: 
  | { [],[], [] }
  | LBRACKET tl = list(TYVAR) MID rl=list(rvar_no_pos) MID el =
    list(effvar_no_pos) RBRACKET 
    { tl, rl, el }

decl:
  | b = letwithoutargs EQUAL t = nterm
    { let p,x,l = b in
      let_wconst l t x NoRec (embrace p t.loc) }
  | b = letwithargs EQUAL body = funcbody
    { let p,x,l,args = b in
      let pre,e,q = body in
      let_wconst l (mk_efflam args (snd pre) e (snd q) p) x 
        NoRec (embrace p e.loc) }
  | b = letwithargs EQUAL t1 = nterm
    { let p,x,l,args = b in
      let_wconst l (mk_pure_lam args t1 p) x NoRec (embrace p t1.loc) }
  | f = letrec { (f : ParseT.t -> ParseT.t) (const (Const.Void) dummy) }
  | p = PARAMETER x = defprogvar_no_pos l = optgen args = arglist 
    COLON rt = ty COMMA e = sepeffect EQUAL pre = precond post = postcond
  { 
    let par = mk_param args (snd pre) (snd post) rt e p in
    let_wconst l par x NoRec (embrace p (fst post))} 
  | p = AXIOM x = defprogvar_no_pos l = optgen COLON t = nterm
    { let_wconst l (mk (Axiom t) p) x NoRec (embrace p t.loc) }
  | p = LOGIC x = defprogvar_no_pos l = optgen COLON t = ty
    { let_wconst l (mk (Logic t) p) x NoRec p }
  | p = TYPE x = progvar_no_pos l = optgen
    { typedef l None x (const (Const.Void) p) p }
  | p = TYPE x = progvar_no_pos l = optgen EQUAL t = ty
    { typedef l (Some t) x (const (Const.Void) p) p }

main: l = nonempty_list(decl) EOF { merge l }
