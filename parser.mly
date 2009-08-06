%{
  open Ptree

  let infix_app s t1 t2 = 
    App (App (Var s, t1), t2)

  let rec merge = function
    | [] -> Const Ast.Void
    | Let (t,x,Const Ast.Void)::xs ->
        Let (t,x,merge xs)
    | _ -> assert false

%}

%token <int> INT
%token LPAREN RPAREN
%token <string> IDENT
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
%token FUN
%token LT
%token TRUE FALSE

%right ARROW
(* %nonassoc ifprec *)
%nonassoc IN
%nonassoc LE LT
%right EQUAL NEQ
%left PLUS MINUS
%right STAR
%start <Ptree.t> main

%%

(*
tconstant:
  | p = BOOL { p, Ty.Bool }
  | p = TINT { p, Ty.Int }
  | p = UNIT { p, Ty.Unit }
  | p = PROP { p, Ty.Prop }

simple_type:
  | x = tconstant { `Const x }
  | v = IDENT { Var v }

ty:
  | t = simple_aftype { t }
  | t1 = aftype ARROW t2 = aftype 
    { embrace t1.loc t2.loc (TPureArrow (t1,t2)) }
  | t1 = aftype STAR t2 = aftype 
    { embrace t1.loc t2.loc (TTuple (t1,t2)) }

*)
constant:
  |  n = INT { Ast.Int n }
  |  TRUE { Ast.Btrue }
  |  FALSE { Ast.Bfalse }
  |  VOID { Ast.Void }

%inline infix_arith:
  | MINUS { "Zminus" }
  |  PLUS { "Zplus" }
  |  STAR { "Zmult" }
%inline infix_cmp_prog:
  | LE { "Zleb" }
  | LT { "Zltb" }
  | EQUAL { "beq_z" }

aterm:
  | x = IDENT { Var x }
  | c = constant { Const c }
(*
  | l = LPAREN e = nterm COLON t = aftype r =  RPAREN 
    { embrace l r (PAnnot (e,t)) }
*)
  | LPAREN t = nterm RPAREN { t }

appterm:
  | t = aterm { t }
  | t1 = appterm t2 = aterm { App (t1,t2) }

nterm:
  | t1 = appterm { t1 }
  | t1 = nterm i = infix_arith t2 = nterm  { infix_app i t1 t2 }
  | t1 = nterm i = infix_cmp_prog t2 = nterm  { infix_app i t1 t2 }
  | t1 = nterm  NEQ t2 = nterm { infix_app "<>" t1 t2 }
(*
  | st = IF it = nterm THEN tb = nterm ELSE eb = nterm %prec ifprec
    { embrace st eb.loc (PIte (it,tb,eb)) }
*)
  | FUN x = IDENT ARROW b = nterm { Lam (x,b) }
  | LET x = IDENT EQUAL t1 = nterm IN t2 = nterm 
    { Let (t1,x,t2) }

decl:
  | LET x = IDENT EQUAL t = nterm
    {Let (t,x, Const (Ast.Void))}

main: l = nonempty_list(decl) EOF { merge l }
