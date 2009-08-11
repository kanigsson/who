%{
  open Clean_ast

  let app t1 t2 = mk_node (App (t1,t2))
  let var s = mk_node (Var s)
  let const c = mk_node (Const c)
  let infix_app s t1 t2 = app (app (var s) t1) t2
  let let_ l e1 x e2 = mk_node (Let (l,e1,x,e2))
  let lam x t e = mk_node (Lam (x,t,e))

  let rec merge = function
    | [] -> const Const.Void
    | { v = Let (l,t,x,{ v = Const Const.Void }) }::xs -> let_ l t x (merge xs)
    | _ -> assert false

%}

%token <int> INT
%token LPAREN RPAREN LBRACKET RBRACKET
%token <string> IDENT
%token <string> TYVAR
%token LET IN 
%token VOID
%token PLUS MINUS LE EQUAL STAR NEQ
%token EOF
(*
%token <Loc.loc> EXCLAM ASSIGN
%token REC REF
*)
%token ARROW
(*
%token IF
%token THEN ELSE
*)
%token COLON
%token FUN
%token LT
%token TRUE FALSE BOOL TINT UNIT

%right ARROW
(* %nonassoc ifprec *)
%nonassoc IN
%nonassoc LE LT
%right EQUAL NEQ
%left PLUS MINUS
%right STAR
%start <Clean_ast.t> main

%%

tconstant:
  | BOOL { Const.TBool }
  | TINT { Const.TInt }
  | UNIT { Const.TUnit }

stype:
  | x = tconstant { Ty.const x }
  | v = TYVAR { Ty.var v }

ty:
  | t = stype { t }
  | t1 = ty ARROW t2 = ty 
    { Ty.arrow t1 t2 }
  | t1 = ty STAR t2 = ty 
    { Ty.tuple t1 t2 }

constant:
  |  n = INT { Const.Int n }
  |  TRUE { Const.Btrue }
  |  FALSE { Const.Bfalse }
  |  VOID { Const.Void }

%inline infix_arith:
  | MINUS { "Zminus" }
  |  PLUS { "Zplus" }
  |  STAR { "Zmult" }
%inline infix_cmp_prog:
  | LE { "Zleb" }
  | LT { "Zltb" }
  | EQUAL { "beq_z" }

aterm:
  | x = IDENT { var x }
  | c = constant { const c }
(*
  | l = LPAREN e = nterm COLON t = aftype r =  RPAREN 
    { embrace l r (PAnnot (e,t)) }
*)
  | LPAREN t = nterm RPAREN { t }

appterm:
  | t = aterm { t }
  | t1 = appterm t2 = aterm { app t1 t2 }

nterm:
  | t1 = appterm { t1 }
  | t1 = nterm i = infix_arith t2 = nterm  { infix_app i t1 t2 }
  | t1 = nterm i = infix_cmp_prog t2 = nterm  { infix_app i t1 t2 }
  | t1 = nterm  NEQ t2 = nterm { infix_app "<>" t1 t2 }
  | FUN LPAREN x = IDENT COLON t = ty RPAREN ARROW e = nterm { lam x t e }
  | LET x = IDENT l = optgen EQUAL t1 = nterm IN t2 = nterm 
    { let_ l t1 x t2 }

optgen: 
  | { [] }
  | LBRACKET l = nonempty_list(TYVAR) RBRACKET { l }

decl:
  | LET x = IDENT l = optgen EQUAL t = nterm
  { let_ l t x (const (Const.Void)) }

main: l = nonempty_list(decl) EOF { merge l }
