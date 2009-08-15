%{
  open Loc
  open Ast
  open ParseT
  module SS = Misc.SS

  let list_to_set x = 
    List.fold_left (fun acc x -> SS.add x acc) SS.empty x

  let rec merge = function
    | [] -> const Const.Void Loc.dummy
    | { v = Let (l,t,x,{ v = Const Const.Void }); loc = loc }::xs -> 
        let_ l t x (merge xs) loc
    | { v = TypeDef (l,t,x,{ v = Const Const.Void }); loc = loc }::xs -> 
        typedef l t x (merge xs) loc
    | _ -> assert false

  let embrace inf1 inf2 = { st = inf1.st ; en = inf2.en }

  let mk_lam l p e q loc =
    let l = List.rev l in
    match l with
    | [] -> assert false
    | (x,t)::xs ->
        let acc = lam x t p e q loc in
        List.fold_left (fun acc (x,t) -> pure_lam x t acc loc) acc xs

  let mk_pure_lam l e loc =
    List.fold_right (fun (x,t) acc -> pure_lam x t acc loc) l e

%}

%token <int Loc.t> INT
%token <Loc.loc> LPAREN RPAREN LCURL
%token LBRACKET RBRACKET RCURL
%token <string Loc.t> IDENT
%token <string> TYVAR
%token IN 
%token PLUS MINUS LE EQUAL STAR NEQ BEQUAL BNEQ
%token EOF
%token REF
%token <Loc.loc> EXCLAM DEXCLAM IF FUN TRUE FALSE PTRUE PFALSE VOID LET AXIOM LOGIC TYPE
%token COLON COMMA ASSIGN MID AND THEN ELSE LT GT ARROW BOOL TINT UNIT PROP

%nonassoc let_
%right ARROW
%nonassoc ifprec
%left AND
%nonassoc LE LT
%nonassoc ASSIGN
%right EQUAL NEQ BEQUAL BNEQ
%right COMMA
%left PLUS MINUS
%right STAR

%start <Ast.ParseT.t> main
%%

ident_no_pos: | x = IDENT { x.c }
tconstant:
  | BOOL { Const.TBool }
  | TINT { Const.TInt }
  | UNIT { Const.TUnit }
  | PROP { Const.TProp }

stype:
  | x = tconstant { Ty.const x }
  | v = TYVAR { Ty.var v }

effect:
  | lr = list(ident_no_pos) MID le =  list(ident_no_pos) 
    { list_to_set lr, list_to_set le}
ty:
  | t = stype { t }
  | t1 = ty ARROW t2 = ty { Ty.parr t1 t2 }
  | t1 = ty ARROW LCURL e = effect RCURL t2 = ty %prec ARROW { Ty.arrow t1 t2 e }
  | t1 = ty STAR t2 = ty { Ty.tuple t1 t2 }
  | LT e = effect GT { Ty.map e }
  | REF LPAREN id = ident_no_pos COMMA t = ty  RPAREN { Ty.ref_ id t }

constant:
  |  n = INT    { n.info, Const.Int n.c }
  |  p = TRUE   { p, Const.Btrue }
  |  p = FALSE  { p, Const.Bfalse }
  |  p = PTRUE  { p, Const.Ptrue }
  |  p = PFALSE { p, Const.Pfalse }
  |  p = VOID   { p, Const.Void }

%inline infix:
  | MINUS { "Zminus" }
  |  PLUS { "Zplus" }
  |  STAR { "Zmult" }
  | ASSIGN { ":=" }
  | LE { "Zleb" }
  | LT { "Zltb" }
  | EQUAL { "=" }
  | BEQUAL { "==" }
  | BNEQ { "!=" }
  | NEQ { "<>" }
  | AND { "/\\" }
  | COMMA { "," }
  | ARROW { "->" }

aterm:
  | x = IDENT { var x.c x.info }
  | p = EXCLAM { var "!" p }
  | c = constant { let p,c = c in const c p }
  | l = LPAREN t = nterm e = RPAREN { mk t.v (embrace l e) }

appterm:
  | t = aterm { t }
  | t1 = appterm t2 = aterm { app t1 t2 (embrace t1.loc t2.loc) }

nterm:
  | p = DEXCLAM x = IDENT 
    { app2 "!!" (var x.c x.info) (var "cur" p) (embrace p x.info) }
  | p = DEXCLAM x = IDENT MID t = aterm 
    { app2 "!!" (var x.c x.info) t (embrace p t.loc)  }
  | t1 = appterm { t1 }
  | t1 = nterm i = infix t2 = nterm  
    { app2 i t1 t2 (embrace t1.loc t2.loc) }
  | sp = FUN l = arglist ARROW body = funcbody
    { let p,e,q = body in
      mk_lam l (snd p) e (snd q) (embrace sp (fst q)) }
  | sp = FUN l = arglist ARROW e = nterm 
    { mk_pure_lam l e (embrace sp e.loc) }
  | b = letwithoutargs EQUAL t = nterm IN t2 = nterm %prec let_
    { let p,x,l = b in
      let_ l t x t2 p}
  | b = letwithargs EQUAL body = funcbody IN t2 = nterm %prec let_
    { let p,x,l,args = b in
      let pre,e,q = body in
      let_ l (mk_lam args (snd pre) e (snd q) p) x t2 (embrace p t2.loc) }
  | b = letwithargs EQUAL t1 = nterm IN t2 = nterm %prec let_
    { let p,x,l,args = b in
      let_ l (mk_pure_lam args t1 p) x t2 (embrace p t2.loc) }
  | st = IF it = nterm THEN tb = nterm ELSE eb = nterm %prec ifprec
    { mk (Ite(it,tb,eb)) (embrace st eb.loc) }

onetyarg:
  LPAREN xl = nonempty_list(ident_no_pos) COLON t = ty RPAREN
    { List.map (fun x -> x,t) xl }

arglist: l = nonempty_list(onetyarg) { List.flatten l }

letwithargs:
  | p = LET x = ident_no_pos l = optgen args = arglist
  { p, x, l, args }

letwithoutargs:
  | p = LET x = ident_no_pos l = optgen 
    { p,x,l }

funcbody:
  p = precond e = nterm q = postcond { p,e,q }

postcond:
  | p = LCURL RCURL { p, PNone }
  | p = LCURL t = nterm RCURL { p, PPlain t}
  | p = LCURL x = ident_no_pos COLON t = nterm RCURL { p, PResult (x,t)}

precond:
  | p = LCURL RCURL { p, None }
  | p = LCURL t = nterm RCURL { p, Some t}

optgen: 
  | { [],[], [] }
  | LBRACKET tl = list(TYVAR) MID rl=list(ident_no_pos) MID el = list(ident_no_pos) RBRACKET 
    { tl, rl, el }

decl:
  | b = letwithoutargs EQUAL t = nterm
    { let p,x,l = b in
      let_ l t x  (const (Const.Void) p) (embrace p t.loc) }
  | b = letwithargs EQUAL body = funcbody
    { let p,x,l,args = b in
      let pre,e,q = body in
      let_ l (mk_lam args (snd pre) e (snd q) p) x (const (Const.Void) p) 
        (embrace p e.loc) }
  | b = letwithargs EQUAL t1 = nterm
    { let p,x,l,args = b in
      let_ l (mk_pure_lam args t1 p) x (const (Const.Void) p) (embrace p t1.loc) }
  | p = AXIOM x = ident_no_pos l = optgen EQUAL t = nterm
    { let_ l (mk (Axiom t) p) x (const (Const.Void) p) (embrace p t.loc) }
  | p = LOGIC x = ident_no_pos l = optgen EQUAL t = ty
    { let_ l (mk (Logic t) p) x (const (Const.Void) p) p }
  | p = TYPE x = ident_no_pos l = optgen
    { typedef l None x (const (Const.Void) p) p }
  | p = TYPE x = ident_no_pos l = optgen EQUAL t = ty
    { typedef l (Some t) x (const (Const.Void) p) p }

main: l = nonempty_list(decl) EOF { merge l }
