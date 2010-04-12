(******************************************************************************)
(*                                                                            *)
(*                      Who                                                   *)
(*                                                                            *)
(*       A simple VCGen for higher-order programs.                            *)
(*                                                                            *)
(*  Copyright (C) 2009, 2010, Johannes Kanig                                  *)
(*  Contact: kanig@lri.fr                                                     *)
(*                                                                            *)
(*  Who is free software: you can redistribute it and/or modify it under the  *)
(*  terms of the GNU Lesser General Public License as published by the Free   *)
(*  Software Foundation, either version 3 of the License, or any later        *)
(*  version.                                                                  *)
(*                                                                            *)
(*  Who is distributed in the hope that it will be useful, but WITHOUT ANY    *)
(*  WARRANTY; without even the implied warranty of MERCHANTABILITY or         *)
(*  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public      *)
(*  License for more details.                                                 *)
(*                                                                            *)
(*  You should have received a copy of the GNU Lesser General Public License  *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>      *)
(******************************************************************************)

%{
  (** TODO compute the type of a recursive function by the given return type and
   * the argument types *)
  open Loc
  open Const
  open ParseTree
  module I = Identifiers

  (* build a new location out of two old ones by forming the large region
  containing both *)
  (* take a nonempty list of variable bindings l and a function [f] and
  build [λv1:t1 ... λv(n-1):t(n-1).u], where [u] is the result of [f vn tn];
  all lambdas are pure. *)
  let mk_lam f (l : (string * ty option) list) loc =
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
  let mk_efflam l cap p e q = mk_lam (fun x t ->
    let t =
      try Opt.force t
      with Invalid_argument "force" ->
        failwith "type annotation obligatory for lambda" in
    lamcap x t cap p e q) l

  (* construct a sequence of pure lambdas on top of a parameter with type [rt]
     and effect [eff]; the innermost lambda is effectful as in [mk_efflam] *)
  let mk_param l cap p q rt eff loc =
    mk_efflam l cap p (mk (Param (rt,eff)) loc) q loc

  (* construct a sequence of quantifiers on top of [e] *)
  let mk_quant k l e loc =
    List.fold_right (fun (x,t) acc -> quant k x t acc loc) l e

  (* remove location information from a list of annotated values *)
  (* build a for loop *)
  let forfunction dir i start end_ inv body pos =
    let s = "__start" and e = "__end" in
    let forterm = mk (For (dir,inv,i.c,s,e,body)) pos in
    let em = [],[],[] in
    (* let start = start and end_ = end_ in
       forvar inv start end_ body *)
    let_ em start s (let_ em end_ e forterm NoRec end_.loc)
      NoRec start.loc


%}

%start <ParseTree.theory> main
%%

(* basic terms *)

protected_term:
  | l = LPAREN t = seq_term e = RPAREN { mk t.v (embrace l e) }
  | l = LPAREN e = seq_term COLON t = ty r = RPAREN
    { mk (Annot (e,t)) (embrace l r) }

aterm:
  | p = VOID { var I.void_id p }
  | p = REF { var "ref" p}
  | p = prefix x = IDENT
    { app (var (snd p) (fst p)) (var x.c x.info) (embrace (fst p) x.info) }
  | x = IDENT AT e = sepeffect
    { mk (Restrict (var x.c x.info,e)) x.info }
  | p = DEXCLAM x = IDENT
    { mk (Get (var x.c x.info, var "cur" p)) (embrace p x.info) }
  | p = DEXCLAM x = IDENT AT t = aterm
    { mk (Get (var x.c x.info, t)) (embrace p t.loc) }
  | x = IDENT { var x.c x.info }
  | x = IDENT LBRACKET inst = sepeffect* RBRACKET { var ~inst x.c x.info }
  | l = LPAREN x = prefix r = RPAREN
    { var (snd x) (embrace l r) }
  | c = constant { let p,c = c in const c p }
  | l = LPAREN x = infix e = RPAREN { var (snd x) (embrace l e) }
  | t = protected_term { t }

tuple_list:
  | t1 = nterm COMMA t2 = nterm { [t2; t1] }
  | tl = tuple_list COMMA t1 = nterm { t1 :: tl }


seq_term:
  | t = nterm %prec below_SEMI { t }
  | t1 = nterm SEMICOLON t2 = seq_term
    { mk (Seq (t1,t2)) (embrace t1.loc t2.loc) }

(* all the more complex terms *)
nterm:
  | t = aterm { t }
  | t = aterm l = aterm+
    { appn t l }
  | t1 = aterm DLCURL l = IDENT* DRCURL tl = aterm+
    { cap_appn t1 tl (strip_info l) }
  | tl = tuple_list %prec below_COMMA
    {
      let n = List.length tl in
      let tl = List.rev tl in
      appni (Identifiers.mk_tuple_id n) tl (List.hd tl).loc
    }
  | t1 = nterm i = infix t2 = nterm
    { appi (snd i) t1 t2 (embrace t1.loc t2.loc) }
  | sp = FUN l = arglist ARROW body = funcbody
    { let cap, p,e,q = body in
      mk_efflam l cap (snd p) e (snd q) (embrace sp (fst q)) }
  | sp = FUN l = arglist ARROW e = seq_term
    { mk_pure_lam l e (embrace sp e.loc) }
  | st = IF it = seq_term THEN tb = nterm ELSE eb = nterm
    { mk (Ite(it,tb,eb)) (embrace st eb.loc) }
  (* a local let is like a global one, but with an IN following *)
  | f = alllet IN e2 = seq_term
    { let g, e, x, r = f in let_ g e x e2 r e2.loc }
  | p = LETREGION l = IDENT* IN t = seq_term
    { mk (LetReg (strip_info l,t)) p }
  | st = FOR i = IDENT EQUAL e1 = seq_term dir = todownto e2 = seq_term DO
       p = precond
       e3 = seq_term
    en = DONE
    { forfunction dir i e1 e2 (snd p) e3 (embrace st en) }
  | sp = FORALL l = arglist DOT e = nterm %prec forall
    { mk_quant `FA l e (embrace sp e.loc) }
  | sp = EXISTS l = arglist DOT e = nterm %prec forall
    { mk_quant `EX l e (embrace sp e.loc) }
  | l = DLBRACKET p = nterm? DRBRACKET
     e = nterm
    DLBRACKET q = postcond_int r = DRBRACKET
    { mk (HoareTriple (p,e,q)) (embrace l r) }

todownto:
  | TO { "forto" }
  | DOWNTO { "fordownto" }

onetyarg:
  | LPAREN xl = defprogvar_no_pos+ COLON t = ty RPAREN
    { List.map (fun x -> x,Some t) xl }
  | x = IDENT { [x.c, None] }


arglist: l = onetyarg+ { List.flatten l }
may_empty_arglist: l = onetyarg* { List.flatten l}

(* the common part of every let binding *)
letcommon:
  | p = LET x = defprogvar_no_pos l = gen args = may_empty_arglist EQUAL
    { p, x ,l,args }

alllet:
(* the simplest case *)
  | b = letcommon t = seq_term
    { let p,x,l,args = b in
      l, mk_pure_lam args t p, x, NoRec }
(* the function definition case *)
  | b = letcommon body = funcbody
    { let p,x,l,args = b in
      let cap, pre,e,q = body in
      if args = [] then $syntaxerror;
      l, mk_efflam args cap (snd pre) e (snd q) p, x, NoRec
    }
(* the recursive function definition case *)
  | p = LET REC l = gen LPAREN x = defprogvar_no_pos
    COLON t = ty RPAREN args = arglist EQUAL b = funcbody
    { let cap, pre,e,q = b in
      l, mk_efflam args cap (snd pre) e (snd q) p, x, Rec t
    }

funcbody:
  cap = maycapdef p = precond e = seq_term q = postcond { cap, p,e,q }

postcond_int:
  | {PNone }
  | t = nterm { PPlain t }
  | x = defprogvar_no_pos COLON t = nterm { PResult (x,t) }

postcond: l = LCURL q = postcond_int r = RCURL { embrace l r, q }

precond: | p = LCURL t = nterm? RCURL { p, t }

(* a declaration is either
  - a let
  - a parameter
  - an axiom
  - a logic
  - a typedef
  - a region definition
  - a section
  *)

param_annot:
  | t = ty e = sep_readwrite { t, e}
  | t = ty COMMA e = sep_readwrite { t, e}
  | e = sep_readwrite t = ty { t, e}
  | e = sep_readwrite COMMA t = ty { t, e }

decl:
  | g = alllet
    { let g, e, x, r = g in Program (x,g,e,r) }
  | p = PARAMETER x = defprogvar_no_pos l = gen COLON rt = ty
    { let par = mk (Param (rt,rw_empty)) p in
      Program (x,l,par,NoRec) }
  | p = PARAMETER x = defprogvar_no_pos l = gen args = arglist
    COLON ann = param_annot EQUAL
      cap = maycapdef pre = precond post = postcond
  {
    let rt, e = ann in
    let par = mk_param args cap (snd pre) (snd post) rt e p in
    Program (x,l,par,NoRec)
  }
  | AXIOM x = defprogvar_no_pos l = gen COLON t = nterm
    { Axiom (x, l, t) }
  | GOAL x = defprogvar_no_pos l = gen COLON t = nterm
    { Goal (x, l, t) }
  | LOGIC x = defprogvar_no_pos l = gen COLON t = ty
    { Logic (x,l,t) }
  | TYPE x = IDENT l = gen
    { TypeDef (x.c, l, Abstract ) }
  | TYPE x = IDENT l = gen EQUAL t = ty
    { TypeDef (x.c, l,Alias t) }
  | TYPE x = IDENT l = gen EQUAL MID bl = separated_nonempty_list(MID,branch)
    { TypeDef (x.c,l,ADT bl) }
  | LETREGION l = IDENT* { DLetReg (strip_info l) }
  | SECTION x = IDENT fn = takeoverdecl* l = decl+ END
    { Section (x.c, fn, l) }
  | INDUCTIVE x = IDENT l = gen tl = separated_nonempty_list(ARROW,stype) EQUAL 
    option(MID) tel = separated_list(MID,nterm) END
    { Inductive (x.c,l,tl,tel) }

branch:
    | x = IDENT  { x.c, []}
    | x = IDENT OF tl = separated_nonempty_list(STAR,stype) { x.c, tl }

(* a program is simply a list of declarations; we call [to_abst_ast] to
  obtain a single AST *)
main: l = decl* EOF { l }
