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

  let unit = Loc.mk Loc.dummy (TVar "unit")

  (* build a new location out of two old ones by forming the large region
  containing both *)
  (* take a nonempty list of variable bindings l and a function [f] and
  build [λv1:t1 ... λv(n-1):t(n-1).u], where [u] is the result of [f vn tn];
  all lambdas are pure. *)
  let mk_lam f (l : (string option * ty option) list) loc =
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
  let mk_efflam l p e q = mk_lam (fun x t ->
    let t =
      try Opt.force t
      with Invalid_argument "force" ->
        failwith "type annotation obligatory for lambda" in
    lam x t p e q) l

  (* construct a sequence of pure lambdas on top of a parameter with type [rt]
     and effect [eff]; the innermost lambda is effectful as in [mk_efflam] *)
  let mk_param l p q rt eff loc =
    mk_efflam l p (Loc.mk loc (Param (rt,eff))) q loc

  (* construct a sequence of quantifiers on top of [e] *)
  let mk_quant k l e loc =
    List.fold_right (fun (x,t) acc -> quant k x t acc loc) l e

  (* build a for loop *)

  let may_annot annot e =
    match annot with
    | None -> e
    | Some t -> Loc.mk e.info (Annot (e,t))

  let rec_annot args (t,eff) l =
    let argtys = List.rev_map snd args in
    match argtys with
    | [] -> failwith "recursive objects must be functions"
    | None:: _ ->
        failwith "annotation needed for arguments of recursive functions"
    | Some x::xs ->
        List.fold_left (fun acc t ->
          match t with
          | None ->
              failwith "annotation needed for arguments of recursive functions"
          | Some t -> purearrow t acc l) (effarrow x t eff l) xs

%}

%start <ParseTree.theory> main
%%

(* basic terms *)

term_inst:
  | LBRACKET e = sepeffect* RBRACKET { ([],[],e) }
  | LBRACKET tl = separated_list(COMMA,ty) MID rl = IDENT*
    MID el = sepeffect* RBRACKET
    { (tl, rl, el) }

aterm_nopos:
  | VOID { Var (I.void_id,([],[],[])) }
  | p = annotated_inl(prefix) t = aterm { App (var p.c p.info, t) }
  | p = annotated_inl(prefix) inst = term_inst t = aterm
    { App (var ~inst p.c p.info ,t) }
  | x = annotated(IDENT) AT e = sepeffect { Restrict (var x.c x.info,e) }
  | DEXCLAM x = annotated(IDENT) { Get (var x.c x.info, var "cur" x.info) }
  | DEXCLAM x = annotated(IDENT) AT t = aterm { Get (var x.c x.info, t) }
  | x = IDENT { Var (x,([],[],[])) }
  | x = CONSTRUCTOR { Var (x, ([],[],[])) }
  | x = IDENT inst = term_inst { Var (x,inst) }
  | LPAREN x = prefix RPAREN { Var (x, ([],[],[])) }
  | c = constant { Const c }
  | LPAREN x = infix RPAREN { Var (x, ([],[],[])) }
  | LPAREN t = seq_term RPAREN { t.c }
  | BEGIN t = seq_term END { t.c }
  | LPAREN e = seq_term COLON t = ty RPAREN { Annot (e,t) }
  | REF LPAREN r = IDENT RPAREN { ParseTree.Ref r }
aterm: t = annotated(aterm_nopos) { t }

tuple_list:
  | t1 = nterm COMMA t2 = nterm { [t2; t1] }
  | tl = tuple_list COMMA t1 = nterm { t1 :: tl }


seq_term:
  | t = nterm %prec below_SEMI { t }
  | t1 = nterm SEMICOLON t2 = seq_term
    { Loc.mk (Loc.join_with t1 t2) (Seq (t1,t2)) }

(* all the more complex terms *)
nterm_nopos:
  | t = aterm_nopos { t }
  | t = aterm l = aterm+ { (appn t l).Loc.c }
  | tl = tuple_list %prec below_COMMA
    {
      let n = List.length tl in
      let tl = List.rev tl in
      (appni (Identifiers.mk_tuple_id n) tl (List.hd tl).info).c
    }
  | t1 = nterm i = annotated_inl(infix) t2 = nterm
    { let pos1 = Loc.embrace t1.info i.info in
      App (Loc.mk pos1 (App(var i.c i.info, t1)), t2) }
  | FUN l = arglist ARROW body = annotated(funcbody)
    { let p,e,q = body.c in
      (mk_efflam l p e q (left_join $startpos body.info)).c }
  | FUN l = arglist ARROW e = seq_term
    { (mk_pure_lam l e (left_join $startpos e.info)).c }
  | IF it = seq_term THEN tb = nterm ELSE eb = nterm
    { Ite(it,tb,eb) }
  (* a local let is like a global one, but with an IN following *)
  | f = alllet IN e2 = seq_term
    { let g, e, x, r = f in Let (g,e,fst x,e2,r) }
  | LETREGION l = IDENT* IN t = seq_term
    { LetReg (l,t) }
  | FOR i = IDENT EQUAL e1 = seq_term dir = todownto e2 = seq_term DO
       p = precond
       e3 = seq_term
    DONE
    { For (dir,p,i,e1,e2,e3) }
  | FORALL g = gen DOT e = nterm %prec forall
    { Gen (g,e) }
  | FORALL l = arglist DOT e = nterm %prec forall
    { (mk_quant `FA l e (left_join $startpos e.info)).c }
  | EXISTS l = arglist DOT e = nterm %prec forall
    { (mk_quant `EX l e (left_join $startpos e.info)).c }
  | DLBRACKET p = nterm? DRBRACKET
     e = nterm
    DLBRACKET q = postcond_int DRBRACKET
    { HoareTriple (p,e,q) }
  | MATCH t = seq_term WITH option(MID)
    bl = separated_nonempty_list(MID,branch) END
    { Case (t, bl) }
  | PARAMETER LPAREN t = ty COMMA e = sep_readwrite RPAREN
    { Param (t,e) }

nterm: t = annotated(nterm_nopos) { t }

branch: p = pattern ARROW e = seq_term { p, e }

basic_pattern:
  | x = IDENT { PVar (Some x)  }
  | UNDERSCORE { PVar None }
  | x = CONSTRUCTOR { PApp (x,[]) }

pattern_nopos:
  | p = basic_pattern { p }
  | x = CONSTRUCTOR p = annotated(basic_pattern) { PApp(x,[p]) }
  | x = CONSTRUCTOR LPAREN pl = separated_list(COMMA, pattern) RPAREN
    { PApp(x,pl) }
pattern: p = annotated(pattern_nopos) { p }

todownto:
  | TO { "forto" }
  | DOWNTO { "fordownto" }

funargvar:
  | x = IDENT { Some x }
  | UNDERSCORE { None }

onetyarg:
  | LPAREN xl = funargvar+ COLON t = ty RPAREN
    { List.map (fun x -> x,Some t) xl }
  | x = IDENT { [Some x, None] }
  | UNDERSCORE { [None, None ] }
  | VOID { [None, Some unit] }


arglist: l = onetyarg+ { List.flatten l }
may_empty_arglist: l = onetyarg* { List.flatten l}
may_tyannot :
  | { None }
  | COLON t = ty { Some t }
(* the common part of every let binding *)
letcommon:
  | LET x = defprogvar l = gen args = may_empty_arglist
    t = may_tyannot EQUAL
    { x ,l,args, t }

alllet:
(* the simplest case *)
  | b = annotated(letcommon) t = seq_term
    { let x,l,args, annot = b.c in
      let t = may_annot annot t in
      l, mk_pure_lam args t b.info, x,  NoRec }
(* the function definition case *)
  | b = annotated(letcommon) body = funcbody
    { let x,l,args, annot = b.c in
      let pre,e,q = body in
      let e = may_annot annot e in
      if args = [] then $syntaxerror;
      l, mk_efflam args pre e q b.info, x, NoRec
    }
(* the recursive function definition case *)
  | LET REC x = defprogvar l = gen args = arglist
    COLON pt = param_annot EQUAL b = funcbody
    {
      let p = build $startpos $endpos in
      let t = rec_annot args pt p in
      let pre,e,q = b in
      l, mk_efflam args pre e q p, x, Rec t
    }

funcbody:
  p = precond e = seq_term q = postcond { p,e,q }

postcond_int:
  | {PNone }
  | t = nterm { PPlain t }
  | x = IDENT COLON t = nterm { PResult (x,t) }

postcond: LCURL q = postcond_int RCURL { q }

precond: | LCURL t = nterm? RCURL { t }

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
    { let g, e, x, r = g in Program (fst x,g,e, r, snd x) }
  | PARAMETER x = defprogvar l = gen COLON rt = ty
    {
      let p = build $startpos $endpos in
      let par = Loc.mk p (Param (rt,rw_empty)) in
      Program (fst x,l,par, NoRec, snd x) }
  | PARAMETER x = defprogvar l = gen args = arglist
    COLON ann = param_annot EQUAL pre = precond post = postcond
  {
    let rt, e = ann in
    let p = build $startpos $endpos in
    let par = mk_param args pre post rt e p in
    Program (fst x,l,par, NoRec, snd x)
  }
  | AXIOM x = IDENT l = gen COLON t = nterm
    { Axiom (x, l, t) }
  | GOAL x = IDENT l = gen COLON t = nterm
    { Goal (x, l, t) }
  | LEMMA x = IDENT l = gen COLON t = nterm
    { Lemma (x, l, t) }
  | LOGIC x = defprogvar l = gen COLON t = ty
    { Logic (fst x,l,t, snd x) }
  | TYPE x = IDENT l = gen
    { TypeDef (x, l, Abstract ) }
  | TYPE x = IDENT l = gen EQUAL t = ty
    { TypeDef (x, l,Alias t) }
  | TYPE x = IDENT l = gen EQUAL MID bl =
    separated_nonempty_list(MID,constructorbranch)
    { TypeDef (x,l,ADT bl) }
  | LETREGION l = IDENT* { DLetReg (l) }
  | SECTION x = IDENT fn = takeoverdecl* l = decl+ END
    { Section (x, fn, l) }
  | INDUCTIVE x = IDENT l = gen tl = separated_nonempty_list(COMMA,stype) EQUAL
    option(MID) tel = separated_list(MID,inductive_branch) END
    { Inductive (x,l,tl,tel) }

inductive_branch: x = IDENT COLON t = nterm { x, t }

constructorbranch:
    | x = CONSTRUCTOR  { x, []}
    | x = CONSTRUCTOR OF tl = separated_nonempty_list(STAR,stype) { x, tl }

(* a program is simply a list of declarations; we call [to_abst_ast] to
  obtain a single AST *)
main: l = decl* EOF { l }
