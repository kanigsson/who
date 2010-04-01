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
  | TINT { Const.TInt }
  | PROP { Const.TProp }

%public gen:
  | LBRACKET tl = TYVAR* MID rl=IDENT* MID el = TYVAR* RBRACKET
    { tl, strip_info rl, el }
  | LBRACKET tl = TYVAR* RBRACKET { tl, [], [] }
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
  | LBRACKET tl = separated_list(COMMA,ty) MID rl = IDENT*
    MID el = sepeffect* RBRACKET
    { tl, strip_info rl, el }
  | LBRACKET tl = separated_list(COMMA,ty) RBRACKET
    { tl, [] ,[] }

(* basic types *)
stype:
  | x = tconstant { TConst x }
  | v = TYVAR { TVar v }
  | LPAREN t = ty RPAREN { t }
  | v = IDENT i = inst { TApp (v.c,i)  }
  | v = IDENT { TApp (v.c,([],[],[])) }
  | t = stype v = IDENT {TApp (v.c,([t],[],[])) }
  | LPAREN t = ty COMMA l = separated_list(COMMA,ty) RPAREN v = IDENT
    { TApp(v.c,(t::l,[],[])) }

rvar_or_effectvar:
  | x = IDENT { `Rvar x.c }
  | e = TYVAR { `Effvar e }

maycap:
  | { [] }
  | MID l = IDENT* { strip_info l }

effect: | l = rvar_or_effectvar* {partition_effect l }

read_write :
  | e1 = effect PLUS e2 = effect { e1, e2}
  | e = effect { e,e }
%public sep_readwrite_create :
  | LCURL e = read_write cl = maycap RCURL { e, cl}

%public sepeffect:
  | LCURL e = effect RCURL { e }
%public sep_readwrite:
  | LCURL e = read_write RCURL { e }


(* more complex types *)
%public ty:
  | t = stype { t }
  | t1 = ty ARROW t2 = ty { PureArr (t1, t2) }
  | t1 = ty ARROW e = sep_readwrite_create t2 = ty %prec ARROW
    { let e,cl = e in Arrow (t1,t2,e,cl) }
  | tl = product_ty { Tuple tl }
  | LT e = effect GT { Map e }
  | DLBRACKET t = ty DRBRACKET { ToLogic t }
  | REF LPAREN id = IDENT COMMA t = ty  RPAREN { Ref (id.c,t) }

product_ty:
  | t1 = stype STAR t2 = stype { [t1;t2] }
  | t1 = stype STAR tl = product_ty { t1 :: tl }

%public maycapdef:
  | {[] }
  | ALLOCATES l = IDENT+ { (strip_info l) }

