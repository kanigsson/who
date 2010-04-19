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
  open Loc
  open Const
  open ParseTypes

  let partition_effect l =
    List.fold_right (fun x (rl,el) ->
      match x with
      | `Rvar r -> r ::rl, el
      | `Effvar e -> rl, e::el) l ([],[])

%}
%%

(* a program variable which can be used in declarations *)
%public defprogvar:
  | x = IDENT { x }
  | x = infix { { c = snd x; info = fst x } }
  | x = prefix { { c = snd x; info = fst x } }
  | p = REF { Loc.mk p "ref" }
  | p = DEXCLAM { Loc.mk p "!!" }

%public defprogvar_no_pos : x = defprogvar { x.c }
%public tconstant:
  | p = TINT { Const.TInt, p }
  | p = PROP { Const.TProp, p }

%public gen:
  | LBRACKET tl = TYVAR* MID rl=IDENT* MID el = TYVAR* RBRACKET
    { strip_info tl, strip_info rl, strip_info el }
  | LBRACKET tl = TYVAR* RBRACKET { strip_info tl, [], [] }
  | { [], [], [] }

(* infix operators - can be used in definitions *)
%public %inline infix:
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
  | p = ARROW      { p,"->" }
  | p = BLE         { p,"<<=" }
  | p = BGE         { p,">>=" }
  | p = BGT         { p,">>" }
  | p = BLT         { p,"<<" }

(* prefix operators - can be used in definitions *)
%public prefix:
  | p = EXCLAM { p, "!" }
  | p = TILDE { p, "~" }

%public constant:
  | n = INT    { n.info, Const.Int n.c }
  | p = PTRUE  { p, Const.Ptrue }
  | p = PFALSE { p, Const.Pfalse }

takeover:
  | PREDEFINED { Predefined }
  | TAKEOVER { TakeOver }
  | fn = STRING { Include fn }

prover:
  | COQ { `Coq }
  | PANGOLINE { `Pangoline }

%public takeoverdecl:
  | p = prover t = takeover { p, t }

%public inst:
  | p1 = LBRACKET tl = separated_list(COMMA,ty) MID rl = IDENT*
    MID el = sepeffect* p2 = RBRACKET
    { (tl, strip_info rl, el), embrace p1 p2 }
  | p1 = LBRACKET tl = separated_list(COMMA,ty) p2 = RBRACKET
    { (tl, [] ,[]), embrace p1 p2 }

(* basic types *)
%public stype:
  | x = tconstant { let x, p = x in mkty (TConst x) p }
  | v = TYVAR { mkty (TVar v.c) v.info }
  | LPAREN t = ty RPAREN { t }
  | v = IDENT i = inst
    { let i, p =  i in mkty (TApp (v.c,i)) (embrace v.info p) }
  | v = IDENT { mkty (TApp (v.c,([],[],[]))) v.info }
  | t = stype v = IDENT
    { mkty (TApp (v.c,([t],[],[]))) (embrace t.tloc v.info) }
  | p1 = LPAREN t = ty COMMA l = separated_list(COMMA,ty) RPAREN v = IDENT
    { mkty (TApp(v.c,(t::l,[],[]))) (embrace p1 v.info) }

rvar_or_effectvar:
  | x = IDENT { `Rvar x.c }
  | e = TYVAR { `Effvar e.c }

effect: 
  | l = rvar_or_effectvar*
  { partition_effect l }

read_write :
  | e1 = effect PLUS e2 = effect { e1, e2}
  | e = effect { e,e }

%public sepeffect:
  | LCURL e = effect RCURL { e }
%public sep_readwrite:
  | LCURL e = read_write RCURL { e }


(* more complex types *)
%public ty:
  | t = stype { t }
  | t1 = ty ARROW t2 = ty { mkty (PureArr (t1, t2)) (embrace t1.tloc t2.tloc) }
  | t1 = ty ARROW e = sep_readwrite t2 = ty %prec ARROW
    { mkty (Arrow (t1,t2,e)) (embrace t1.tloc t2.tloc)  }
  | tl = product_ty
    { let fst = List.hd tl and last = List.hd (List.rev tl) in
      mkty (Tuple tl) (embrace fst.tloc last.tloc) }
  | p1 = LT e = effect p2 = GT { mkty (Map e) (embrace p1 p2) }
  | p1 = DLBRACKET t = ty p2 = DRBRACKET { mkty (ToLogic t) (embrace p1 p2) }
  | p1 = REF LPAREN id = IDENT COMMA t = ty  p2 = RPAREN
    { mkty (Ref (id.c,t)) (embrace p1 p2) }

product_ty:
  | t1 = stype STAR t2 = stype { [t1;t2] }
  | t1 = stype STAR tl = product_ty { t1 :: tl }
