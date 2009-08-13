%{
  open Clean_ast
  module SS = Misc.SS

  let app t1 t2 = mk_node (App (t1,t2))
  let var s = mk_node (Var s)
  let const c = mk_node (Const c)
  let app2 s t1 t2 = app (app (var s) t1) t2
  let let_ l e1 x e2 = mk_node (Let (l,e1,x,e2))
  let lam x t e = mk_node (Lam (x,t,e))

  let list_to_set x = 
    List.fold_left (fun acc x -> SS.add x acc) SS.empty x

  let read t = app (var "!") t
  let write t1 t2 = app2 ":=" t1 t2

  let rec merge = function
    | [] -> const Const.Void
    | { v = Let (l,t,x,{ v = Const Const.Void }) }::xs -> let_ l t x (merge xs)
    | _ -> assert false

%}

%token <int> INT
%token LPAREN RPAREN LBRACKET RBRACKET LCURL RCURL
%token <string> IDENT
%token <string> TYVAR
%token LET IN 
%token VOID
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
%token COLON COMMA ASSIGN EXCLAM MID
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

effect:
  | lr = list(IDENT) MID le =  list(IDENT) 
    { list_to_set lr, list_to_set le}
ty:
  | t = stype { t }
  | t1 = ty ARROW LCURL e = effect RCURL t2 = ty %prec ARROW { Ty.arrow t1 t2 e }
  | t1 = ty STAR t2 = ty { Ty.tuple t1 t2 }
  | REF LPAREN id = IDENT COMMA t = ty RPAREN { Ty.ref_ id t }

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
  | EXCLAM t = aterm { read t }
  | t1 = aterm ASSIGN t2 = aterm {write t1 t2}

nterm:
  | t1 = appterm { t1 }
  | t1 = nterm i = infix_arith t2 = nterm  { app2 i t1 t2 }
  | t1 = nterm i = infix_cmp_prog t2 = nterm  { app2 i t1 t2 }
  | t1 = nterm  NEQ t2 = nterm { app2 "<>" t1 t2 }
  | FUN LPAREN x = IDENT COLON t = ty RPAREN ARROW e = nterm { lam x t e }
  | LET x = IDENT l = optgen EQUAL t1 = nterm IN t2 = nterm 
    { let_ l t1 x t2 }

optgen: 
  | { [],[], [] }
  | LBRACKET tl = list(TYVAR) MID rl=list(IDENT) MID el = list(IDENT) RBRACKET 
    { tl,rl,el }

decl:
  | LET x = IDENT l = optgen EQUAL t = nterm
  { let_ l t x (const (Const.Void)) }

main: l = nonempty_list(decl) EOF { merge l }
