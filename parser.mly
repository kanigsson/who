%{
  open Loc
  open Const
  open Parsetree

  let void = const (Const.Void) Loc.dummy

  (* Syntactically, a program is a list of declarations; 
    In the parser, this is represented by two different forms:
      * Once indeed as an [ast list]
      * later as a nesting of the following constructs (referred to as abstract
      programs):
        - let ... in
        - typedef ... in
        - section ... end in 
        - letreg ... in 
        - Void as terminator
  *)

  (* takes an [ast list] and transforms it into an abstract program *)
  let rec to_abst_ast = function
    | [] -> void
    | { v = Let (p,l,t,x,{ v = Const Const.Void },r); loc = loc }::xs -> 
        let_ ~prelude:p l t x (to_abst_ast xs) r loc
    | { v = TypeDef (l,t,x,{ v = Const Const.Void }); loc = loc }::xs -> 
        typedef l t x (to_abst_ast xs) loc
    | {v = Section (n,f,e) ; loc = loc } :: xs ->
        let tail = to_abst_ast xs in
        mk (Section (n,f, concat e (mk (EndSec tail) loc))) loc
(*         append_ast (mk (EndSec tail) loc) e)) loc *)
    | {v = LetReg (l,{v = Const Const.Void}); loc = loc} :: xs ->
        mk (LetReg (l, to_abst_ast xs)) loc
    | _ -> assert false

  (* build a new location out of two old ones by forming the large region
  containing both *)
  (* take a nonempty list of variable bindings l and a function [f] and
  build [λv1:t1 ... λv(n-1):t(n-1).u], where [u] is the result of [f vn tn];
  all lambdas are pure. *)
  let mk_lam f l loc =
    let l = List.rev l in
    match l with
    | [] -> assert false
    | (x,t)::xs ->
        let acc = f x t loc in
        List.fold_left (fun acc (x,t) -> pure_lam x t acc loc) acc xs
        
  (* construct a sequence of pure lambdas on top of [e], using [l] *)
  let mk_pure_lam l e loc = 
    if l = [] then e else mk_lam (fun x t -> pure_lam x t e) l loc

  (* construct a sequence of pure lambdas on top of [e], using [l]; 
    the innermost lambda is effectful, using [p] and [q] as pre and post *)
  let mk_efflam l cap p e q = mk_lam (fun x t -> lamcap x t cap p e q) l

  (* construct a sequence of pure lambdas on top of a parameter with type [rt] 
     and effect [eff]; the innermost lambda is effectful as in [mk_efflam] *)
  let mk_param l cap p q rt eff loc = 
    (* TODO caps for params *)
    mk_efflam l cap p (mk (Param (rt,eff)) loc) q loc

  (* construct a sequence of quantifiers on top of [e] *)
  let mk_quant k l e loc = 
    List.fold_right (fun (x,t) acc -> quant k x t acc loc) l e

  (* build a let-binding with the void terminator; detect if we are in prelude
  mode or not *)
  let let_wconst l t x r p = 
    let_ ~prelude:(!Options.prelude) l t x void r p

  (* remove location information from a list of annotated values *)
  (* build a for loop *)
  let forfunction dir i start end_ inv body pos =
    let s = "-start" and e = "-end" in
    let forterm = mk (For (dir,inv,i.c,s,e,body)) pos in
    let em = [],[],[] in
    (* let start = start and end_ = end_ in 
       forvar inv start end_ body *)
    let_ em start s (let_ em end_ e forterm NoRec end_.loc) 
      NoRec start.loc

%}

%start <Parsetree.t> main
%%

(* basic terms *)
aterm:
  | p = REF { var "ref" p}
  | p = prefix x = IDENT
    { app (var (snd p) (fst p)) (var x.c x.info) (embrace (fst p) x.info) }
  | p = DEXCLAM x = IDENT 
    { app2 "!!" (var x.c x.info) (var "cur" p) (embrace p x.info) }
  | p = DEXCLAM x = IDENT MID t = aterm 
    { app2 "!!" (var x.c x.info) t (embrace p t.loc)  }
  | x = IDENT { var x.c x.info }
  | l = LPAREN x = prefix r = RPAREN 
    { var (snd x) (embrace l r) }
  | c = constant { let p,c = c in const c p }
  | l = LPAREN x = infix e = RPAREN { var (snd x) (embrace l e) }
  | l = LPAREN t = nterm e = RPAREN { mk t.v (embrace l e) }
  | l = LPAREN e = nterm COLON t = ty r = RPAREN { mk (Annot (e,t)) (embrace l r) }

(* applicative terms *)
appterm:
  | t = aterm { t }
  | t1 = appterm DLCURL l = IDENT* DRCURL t2 = aterm 
    {cap_app t1 t2 (strip_info l) (embrace t1.loc t2.loc) }
  | t1 = appterm t2 = aterm { app t1 t2 (embrace t1.loc t2.loc) }

(* all the more complex terms *)
nterm:
  | t1 = appterm { t1 }
  | t1 = appterm SEMICOLON t2 = appterm { mk (Seq (t1,t2)) (embrace t1.loc t2.loc) }
  | t1 = nterm i = infix t2 = nterm  
    { appi (snd i) t1 t2 (embrace t1.loc t2.loc) }
  | sp = FUN l = arglist ARROW body = funcbody
    { let cap, p,e,q = body in
      mk_efflam l cap (snd p) e (snd q) (embrace sp (fst q)) }
  | sp = FUN l = arglist ARROW e = nterm 
    { mk_pure_lam l e (embrace sp e.loc) }
  | sp = FORALL l = arglist DOT e = nterm %prec forall
    { mk_quant `FA l e (embrace sp e.loc) }
  | sp = EXISTS l = arglist DOT e = nterm %prec forall
    { mk_quant `EX l e (embrace sp e.loc) }
  | p = LETREGION l = IDENT* IN t = nterm %prec let_
    { mk (LetReg (strip_info l,t)) p }
  | st = IF it = nterm THEN tb = nterm ELSE eb = nterm %prec ifprec
    { mk (Ite(it,tb,eb)) (embrace st eb.loc) }
  (* a local let is like a global one, but with an IN following *)
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
  LPAREN xl = defprogvar_no_pos+ COLON t = ty RPAREN
    { List.map (fun x -> x,t) xl }


arglist: l = onetyarg+ { List.flatten l }
may_empty_arglist: l = onetyarg* { List.flatten l}

(* the common part of every let binding *)
letcommon:
  | p = LET x = defprogvar_no_pos l = gen args = may_empty_arglist EQUAL
    { p, x ,l,args }

alllet:
(* the simplest case *)
  | b = letcommon t = nterm 
    { let p,x,l,args = b in
      fun t2 -> let_ l (mk_pure_lam args t p) x t2 NoRec (embrace p t2.loc) }
(* the function definition case *)
  | b = letcommon body = funcbody 
    { let p,x,l,args = b in
      let cap, pre,e,q = body in
      if args = [] then $syntaxerror;
      fun t2 -> 
        let_ l (mk_efflam args cap (snd pre) e (snd q) p) x t2 NoRec 
          (embrace p t2.loc) }
(* the recursive function definition case *)
  | p = LET REC l = gen LPAREN x = defprogvar_no_pos 
    COLON t = ty RPAREN args = arglist EQUAL b = funcbody
    { let cap, pre,e,q = b in
      (fun e2 -> let_ l (mk_efflam args cap (snd pre) e (snd q) p) x e2 (Rec t)
        (embrace p e2.loc))
    }
    
funcbody:
  cap = maycapdef p = precond e = nterm q = postcond { cap, p,e,q }

postcond:
  | p = precond { match p with p, None -> p, PNone | p, Some f -> p, PPlain f }
  | p = LCURL x = defprogvar_no_pos COLON t = nterm RCURL { p, PResult (x,t)}

precond:
  | p = LCURL RCURL { p, None }
  | p = LCURL t = nterm RCURL { p, Some t}

(* a declaration is either
  - a let
  - a parameter
  - an axiom
  - a logic
  - a typedef
  - a region definition
  - a section
  *)
decl:
  | f = alllet {(f : t -> t) void }
  | p = PARAMETER x = defprogvar_no_pos l = gen COLON rt = ty
    { let_wconst l (mk (Param (rt,([],[]))) p) x NoRec p}
  | p = PARAMETER x = defprogvar_no_pos l = gen args = arglist 
    COLON rt = ty COMMA e = sepeffect EQUAL 
      cap = maycapdef pre = precond post = postcond
  { 
    let par = mk_param args cap (snd pre) (snd post) rt e p in
    let_wconst l par x NoRec (embrace p (fst post))} 
  | p = AXIOM x = defprogvar_no_pos l = gen COLON t = nterm
    { let_wconst l (mk (Axiom t) p) x NoRec (embrace p t.loc) }
  | p = LOGIC x = defprogvar_no_pos l = gen COLON t = ty
    { let_wconst l (mk (Logic t) p) x NoRec p }
  | p = TYPE x = IDENT l = gen
    { typedef l None x.c void p }
  | p = TYPE x = IDENT l = gen EQUAL t = ty
    { typedef l (Some t) x.c void p }
  | p = LETREGION l = IDENT*
    { mk (LetReg (strip_info l, void)) p  }
  | p1 = SECTION x = IDENT fn = takeoverdecl* l = decl+ p2 = END
    { mk (Section (x.c, fn, to_abst_ast l)) (embrace p1 p2) }

(* a program is simply a list of declarations; we call [to_abst_ast] to
  obtain a single AST *)
main: l = decl* EOF { to_abst_ast l }
