%{
  open Loc
  open Const
  open Parsetree

  let void = const (Const.Void) Loc.dummy

  let rec put_at_end tail x =
    let l = x.loc in
    match x.v with
    | Const Const.Void -> tail
    | Let (p,g,t,x,e,r) -> let_ ~prelude:p g t x (put_at_end tail e) r l
    | TypeDef (g,t,x,e) -> typedef g t x (put_at_end tail e) l
    | Section (n,f,e) -> mk (Section (n,f,put_at_end tail e)) l
    | EndSec t  -> mk (EndSec (put_at_end tail t)) l
    | LetReg (rl,e) -> mk (LetReg (rl, put_at_end tail e)) l
    | _ -> assert false

  let rec merge = function
    | [] -> void
    | { v = Let (p,l,t,x,{ v = Const Const.Void },r); loc = loc }::xs -> 
        let_ ~prelude:p l t x (merge xs) r loc
    | { v = TypeDef (l,t,x,{ v = Const Const.Void }); loc = loc }::xs -> 
        typedef l t x (merge xs) loc
    | {v = Section (n,f,e) ; loc = loc } :: xs ->
        let tail = merge xs in
        mk (Section (n,f, put_at_end (mk (EndSec tail) loc) e)) loc
    | {v = LetReg (l,{v = Const Const.Void}); loc = loc} :: xs ->
        mk (LetReg (l, merge xs)) loc
    | _ -> assert false

  let embrace inf1 inf2 = 
    if inf1 = Loc.dummy then inf2 else
      if inf2 = Loc.dummy then inf1 else
        { st = inf1.st ; en = inf2.en }

  let mk_lam f l loc =
    let l = List.rev l in
    match l with
    | [] -> assert false
    | (x,t)::xs ->
        let acc = f x t loc in
        List.fold_left (fun acc (x,t) -> pure_lam x t acc loc) acc xs
        
  let mk_pure_lam l e loc = 
    if l = [] then e else mk_lam (fun x t -> pure_lam x t e) l loc
  let mk_efflam l p e q = mk_lam (fun x t -> lam x t p e q) l
  let mk_param l p q rt eff loc = 
    mk_efflam l p (mk (Param (rt,eff)) loc) q loc

  let mk_quant k l e loc = 
    List.fold_right (fun (x,t) acc -> quant k x t acc loc) l e

  let let_wconst l t x r p = 
    let_ ~prelude:(!Options.prelude) l t x void r p
  let strip_info l = List.map (fun x -> x.c) l

  let forfunction dir i start end_ inv body pos =
    let s = "-start" and e = "-end" in
    let forterm = mk (For (dir,inv,i.c,s,e,body)) pos in
    let em = [],[],[] in
    (* let start = start and end_ = end_ in 
       forvar inv start end_ body *)
    let_ em start s (let_ em end_ e forterm NoRec end_.loc) 
      NoRec start.loc



%}

%token <Big_int.big_int Loc.t> INT
%token <Loc.loc> LPAREN RPAREN LCURL SECTION END
%token LBRACKET RBRACKET RCURL DLCURL DRCURL PREDEFINED DLBRACKET DRBRACKET
%token <string Loc.t> IDENT
%token <string> TYVAR STRING
%token IN SEMICOLON COQ
%token <Loc.loc> PLUS MINUS EQUAL STAR NEQ BEQUAL BNEQ ARROW COMMA AND OR
%token <Loc.loc> ASSIGN GE GT LE LT REF LETREGION TILDE REGION
%token <Loc.loc> BLE BLT BGT BGE
%token EOF
%token REC
%token <Loc.loc> EXCLAM DEXCLAM IF FUN TRUE FALSE PTRUE PFALSE VOID LET AXIOM
%token <Loc.loc> LOGIC TYPE FORALL EXISTS PARAMETER TO DOWNTO FOR DONE
%token COLON MID THEN ELSE   BOOL TINT UNIT PROP DOT DO

%nonassoc forall
%nonassoc let_
%right ARROW
%nonassoc ifprec
%left AND OR
%nonassoc LE LT GE GT BLE BLT BGT BGE
%nonassoc ASSIGN
%right EQUAL NEQ BEQUAL BNEQ
%right COMMA
%left PLUS MINUS
%right STAR

%start <Parsetree.t> main
%%

defprogvar:
  | x = IDENT { x }
  | x = infix { { c = snd x; info = fst x } }
  | x = prefix { { c = snd x; info = fst x } }
  | p = DEXCLAM { Loc.mk p "!!" }
  
defprogvar_no_pos : x = defprogvar { x.c }
tconstant:
  | BOOL { Const.TBool }
  | TINT { Const.TInt }
  | UNIT { Const.TUnit }
  | PROP { Const.TProp }

stype:
  | x = tconstant { TConst x }
  | v = TYVAR { TVar v }
  | LPAREN t = ty RPAREN { t }
  | v = IDENT i = inst { TApp (v.c,i)  }
  | v = IDENT { TApp (v.c,([],[],[])) }
  | t = stype v = IDENT {TApp (v.c,([t],[],[])) }
  | LPAREN t = ty COMMA l = separated_list(COMMA,ty) RPAREN v = IDENT
    { TApp(v.c,(t::l,[],[])) }

effect:
  | lr = list(IDENT) MID le =  list(IDENT) cl = maycap
    { strip_info lr, strip_info le,  cl}

sepeffect:
  | LCURL e = effect RCURL { e }

ty:
  | t = stype { t }
  | t1 = ty ARROW t2 = ty { PureArr (t1, t2) }
  | t1 = ty ARROW e = sepeffect t2 = ty %prec ARROW 
    { Arrow (t1,t2,e) }
  | t1 = ty STAR t2 = ty { Tuple (t1, t2) }
  | LT e = effect GT { Map e }
  | DLBRACKET t = ty DRBRACKET { ToLogic t }
  | REF LPAREN id = IDENT COMMA t = ty  RPAREN { Ref (id.c,t) }

inst:
  LBRACKET tl = separated_list(COMMA,ty) MID rl = list(IDENT) 
  MID el = list(sepeffect) RBRACKET
  { tl, strip_info rl, el }

maycap:
  | { [] }
  | MID l = list(IDENT) { strip_info l }

constant:
  | n = INT    { n.info, Const.Int n.c }
  | p = TRUE   { p, Const.Btrue }
  | p = FALSE  { p, Const.Bfalse }
  | p = PTRUE  { p, Const.Ptrue }
  | p = PFALSE { p, Const.Pfalse }
  | p = VOID   { p, Const.Void }

%inline infix:
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

prefix:
  | p = EXCLAM { p, "!" }
  | p = REF { p, "ref" }
  | p = TILDE { p, "~" }

aterm:
  | p = DEXCLAM x = IDENT 
    { app2 "!!" (var x.c x.info) (var "cur" p) (embrace p x.info) }
  | p = DEXCLAM x = IDENT MID t = aterm 
    { app2 "!!" (var x.c x.info) t (embrace p t.loc)  }
  | x = IDENT { var x.c x.info }
  | x = prefix { var (snd x) (fst x) }
  | c = constant { let p,c = c in const c p }
(*   | l = LPAREN x = infix e = RPAREN { var (snd x) (embrace l e) } *)
  | l = LPAREN t = nterm e = RPAREN { mk t.v (embrace l e) }
  | l = LPAREN e = nterm COLON t = ty r = RPAREN { mk (Annot (e,t)) (embrace l r) }

appterm:
  | t = aterm { t }
  | t1 = appterm DLCURL l = list(IDENT) DRCURL t2 = aterm 
    {cap_app t1 t2 (strip_info l) (embrace t1.loc t2.loc) }
  | t1 = appterm t2 = aterm { app t1 t2 (embrace t1.loc t2.loc) }

nterm:
  | t1 = appterm { t1 }
  | t1 = appterm SEMICOLON t2 = appterm { mk (Seq (t1,t2)) (embrace t1.loc t2.loc) }
  | t1 = nterm i = infix t2 = nterm  
    { appi (snd i) t1 t2 (embrace t1.loc t2.loc) }
  | sp = FUN l = arglist ARROW body = funcbody
    { let p,e,q = body in
      mk_efflam l (snd p) e (snd q) (embrace sp (fst q)) }
  | sp = FUN l = arglist ARROW e = nterm 
    { mk_pure_lam l e (embrace sp e.loc) }
  | sp = FORALL l = arglist DOT e = nterm %prec forall
    { mk_quant `FA l e (embrace sp e.loc) }
  | sp = EXISTS l = arglist DOT e = nterm %prec forall
    { mk_quant `EX l e (embrace sp e.loc) }
  | p = LETREGION l = list(IDENT) IN t = nterm %prec let_
    { mk (LetReg (strip_info l,t)) p }
  | st = IF it = nterm THEN tb = nterm ELSE eb = nterm %prec ifprec
    { mk (Ite(it,tb,eb)) (embrace st eb.loc) }
  | f = alllet IN e2 = nterm %prec let_ {(f : t -> t) e2 }
  | st = FOR i = IDENT EQUAL e1 = nterm dir = todownto e2 = nterm DO 
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
may_empty_arglist: l = list(onetyarg) { List.flatten l}

letcommon:
  | p = LET x = defprogvar_no_pos l = optgen args = may_empty_arglist EQUAL 
    { p, x ,l,args }

alllet:
  | b = letcommon t = nterm 
    { let p,x,l,args = b in
      fun t2 -> let_ l (mk_pure_lam args t p) x t2 NoRec (embrace p t2.loc) }
  | b = letcommon body = funcbody 
    { let p,x,l,args = b in
      let pre,e,q = body in
      if args = [] then $syntaxerror;
      fun t2 -> 
        let_ l (mk_efflam args (snd pre) e (snd q) p) x t2 NoRec 
          (embrace p t2.loc) }
  | p = LET REC l = optgen LPAREN x = defprogvar_no_pos 
    COLON t = ty RPAREN args = arglist EQUAL b = funcbody
    { let pre,e,q = b in
      (fun e2 -> let_ l (mk_efflam args (snd pre) e (snd q) p) x e2 (Rec t)
        (embrace p e2.loc))
    }
    
funcbody:
  p = precond e = nterm q = postcond { p,e,q }

postcond:
  | p = precond { match p with p, None -> p, PNone | p, Some f -> p, PPlain f }
  | p = LCURL x = defprogvar_no_pos COLON t = nterm RCURL { p, PResult (x,t)}

precond:
  | p = LCURL RCURL { p, None }
  | p = LCURL t = nterm RCURL { p, Some t}

optgen: 
  | { [],[], [] }
  | LBRACKET tl = list(TYVAR) MID rl=list(IDENT) MID el =
    list(IDENT) RBRACKET 
    { tl, strip_info rl, strip_info el }

opt_filename:
  | fn = STRING { Some fn}
  | PREDEFINED { None }
decl:
  | f = alllet {(f : t -> t) void }
  | p = PARAMETER x = defprogvar_no_pos l = optgen args = arglist 
    COLON rt = ty COMMA e = sepeffect EQUAL pre = precond post = postcond
  { 
    let par = mk_param args (snd pre) (snd post) rt e p in
    let_wconst l par x NoRec (embrace p (fst post))} 
  | p = AXIOM x = defprogvar_no_pos l = optgen COLON t = nterm
    { let_wconst l (mk (Axiom t) p) x NoRec (embrace p t.loc) }
  | p = LOGIC x = defprogvar_no_pos l = optgen COLON t = ty
    { let_wconst l (mk (Logic t) p) x NoRec p }
  | p = TYPE x = IDENT l = optgen
    { typedef l None x.c void p }
  | p = TYPE x = IDENT l = optgen EQUAL t = ty
    { typedef l (Some t) x.c void p }
  | p = REGION l = list(IDENT)
    { mk (LetReg (strip_info l, void)) p  }
  | p1 = SECTION x = IDENT COQ fn = opt_filename l = nonempty_list(decl) p2 = END
    { mk (Section (x.c, fn, merge l)) (embrace p1 p2) }

main: l = nonempty_list(decl) EOF { merge l }
