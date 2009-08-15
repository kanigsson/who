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
    | _ -> assert false

  let embrace inf1 inf2 = { st = inf1.st ; en = inf2.en }

%}

%token <int Loc.t> INT
%token <Loc.loc> LPAREN RPAREN 
%token LBRACKET RBRACKET RCURL
%token <Loc.loc> LCURL
%token <string Loc.t> IDENT
%token <string> TYVAR
%token <Loc.loc> LET
%token IN 
%token PLUS MINUS LE EQUAL STAR NEQ
%token EOF
%token REF
(*
%token <Loc.loc> EXCLAM ASSIGN
%token REC REF
*)
%token ARROW
(*
%token IF
%token THEN ELSE
*)
%token <Loc.loc> EXCLAM
%token COLON COMMA ASSIGN MID
%token <Loc.loc> FUN
%token LT GT
%token <Loc.loc> TRUE FALSE PTRUE PFALSE VOID
%token BOOL TINT UNIT

%right ARROW
%nonassoc IN
%nonassoc LE LT
%nonassoc ASSIGN
%right EQUAL NEQ
%left PLUS MINUS
%right STAR

%start <Ast.ParseT.t> main
%%

ident_no_pos: | x = IDENT { x.c }
tconstant:
  | BOOL { Const.TBool }
  | TINT { Const.TInt }
  | UNIT { Const.TUnit }

stype:
  | x = tconstant { Ty.const x }
  | v = TYVAR { Ty.var v }

effect:
  | lr = list(ident_no_pos) MID le =  list(ident_no_pos) 
    { list_to_set lr, list_to_set le}
ty:
  | t = stype { t }
  | t1 = ty ARROW LCURL e = effect RCURL t2 = ty %prec ARROW { Ty.arrow t1 t2 e }
  | t1 = ty STAR t2 = ty { Ty.tuple t1 t2 }
  | LT e = effect GT { Ty.map e }
  | REF LPAREN id = ident_no_pos COMMA t = ty RPAREN { Ty.ref_ id t }

constant:
  |  n = INT    { n.info, Const.Int n.c }
  |  p = TRUE   { p, Const.Btrue }
  |  p = FALSE  { p, Const.Bfalse }
  |  p = PTRUE  { p, Const.Ptrue }
  |  p = PFALSE { p, Const.Pfalse }
  |  p = VOID   { p, Const.Void }

%inline infix_arith:
  | MINUS { "Zminus" }
  |  PLUS { "Zplus" }
  |  STAR { "Zmult" }
  | ASSIGN { ":=" }
  | LE { "Zleb" }
  | LT { "Zltb" }
  | EQUAL { "beq_z" }
  | NEQ { "<>" }

aterm:
  | x = IDENT { var x.c x.info }
  | p = EXCLAM { var "!" p }
  | c = constant { let p,c = c in const c p }
  | l = LPAREN t = nterm e = RPAREN { mk t.v (embrace l e) }

appterm:
  | t = aterm { t }
  | t1 = appterm t2 = aterm { app t1 t2 (embrace t1.loc t2.loc) }

nterm:
  | t1 = appterm { t1 }
  | t1 = nterm i = infix_arith t2 = nterm  
    { app2 i t1 t2 (embrace t1.loc t2.loc) }
  | sp = FUN LPAREN x = ident_no_pos COLON t = ty RPAREN 
    ARROW p = prepost e = nterm q = prepost 
    { lam x t (snd p) e (snd q) (embrace sp (fst q)) }
  | sp = FUN LPAREN x = ident_no_pos COLON t = ty RPAREN ARROW e = nterm 
    { pure_lam x t e (embrace sp e.loc) }
  | p = LET x = ident_no_pos l = optgen EQUAL t1 = nterm IN t2 = nterm 
    { let_ l t1 x t2 (embrace p t2.loc) }

prepost:
  | p = LCURL RCURL { p, None }
  | p = LCURL t = nterm RCURL { p, Some t}

optgen: 
  | { [],[], [] }
  | LBRACKET tl = list(TYVAR) MID rl=list(ident_no_pos) MID el =
      list(ident_no_pos) RBRACKET 
    { tl, rl,el }

decl:
  | p = LET x = ident_no_pos l = optgen EQUAL t = nterm
  { let_ l t x (const (Const.Void) p) p }

main: l = nonempty_list(decl) EOF { merge l }
