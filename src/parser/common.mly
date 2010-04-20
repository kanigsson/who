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

%public annotated(X): t = X { Loc.mk_pos $startpos $endpos t }
%public %inline annotated_inl(X): t = X { Loc.mk_pos $startpos $endpos t }
(* a program variable which can be used in declarations *)
%public defprogvar:
  | x = IDENT { x, `Prefix }
  | x = infix { x, `Infix }
  | x = prefix { x, `Prefix }
  | REF { "ref", `Prefix }
  | DEXCLAM { "!!", `Prefix }

tconstant:
  | TINT { Const.TInt }
  | PROP { Const.TProp }

%public gen:
  | LBRACKET tl = TYVAR* MID rl=IDENT* MID el = TYVAR* RBRACKET
    { tl, rl, el }
  | LBRACKET tl = TYVAR* RBRACKET { tl, [], [] }
  | { [], [], [] }

(* infix operators - can be used in definitions *)
%public %inline infix:
  | GT         { ">" }
  | LT         { "<" }
  | MINUS      { "-" }
  | PLUS       { "+" }
  | STAR       { "*" }
  | ASSIGN     { ":=" }
  | LE         { "<=" }
  | GE         { ">=" }
  | EQUAL      { "=" }
  | BEQUAL     { "==" }
  | BNEQ       { "!=" }
  | NEQ        { "<>" }
  | AND        { "/\\" }
  | OR         { "\\/" }
  | ARROW      { "->" }
  | BLE        { "<<=" }
  | BGE        { ">>=" }
  | BGT        { ">>" }
  | BLT        { "<<" }

(* prefix operators - can be used in definitions *)
%public prefix:
  | EXCLAM { "!" }
  | TILDE  { "~" }

%public constant:
  | n = INT    { Const.Int n }
  | PTRUE  { Const.Ptrue }
  | PFALSE { Const.Pfalse }

takeover:
  | PREDEFINED { Predefined }
  | TAKEOVER { TakeOver }
  | fn = STRING { Include fn }

prover:
  | COQ { `Coq }
  | PANGOLINE { `Pangoline }

%public takeoverdecl:
  | p = prover t = takeover { p, t }

inst:
  | LBRACKET tl = separated_list(COMMA,ty) MID rl = IDENT*
    MID el = sepeffect* RBRACKET
    { (tl, rl, el) }
  | LBRACKET tl = separated_list(COMMA,ty) RBRACKET
    { (tl, [] ,[]) }

(* basic types *)
stype_nopos:
  | x = tconstant { TConst x }
  | v = TYVAR { TVar (v) }
  | LPAREN t = ty_nopos RPAREN { t }
  | v = IDENT i = inst { TApp (v,i) }
  | v = IDENT { TApp (v,([],[],[])) }
  | t = stype v = IDENT { TApp (v,([t],[],[])) }
  | LPAREN t = ty COMMA l = separated_list(COMMA,ty) RPAREN v = IDENT
    { TApp(v,(t::l,[],[])) }

%public stype: t = annotated(stype_nopos) { t }

rvar_or_effectvar:
  | x = IDENT { `Rvar x }
  | e = TYVAR { `Effvar e }

effect: | l = rvar_or_effectvar* { partition_effect l }

read_write :
  | e1 = effect PLUS e2 = effect { e1, e2}
  | e = effect { e,e }

%public sepeffect: | LCURL e = effect RCURL { e }
%public sep_readwrite: | LCURL e = read_write RCURL { e }


(* more complex types *)
ty_nopos:
  | t = stype_nopos { t }
  | t1 = ty ARROW t2 = ty { PureArr (t1,t2) }
  | t1 = ty ARROW e = sep_readwrite t2 = ty %prec ARROW
    { Arrow (t1,t2,e)  }
  | tl = product_ty { Tuple tl }
  | LT e = effect GT { Map e }
  | DLBRACKET t = ty DRBRACKET { ToLogic t }
  | REF LPAREN id = IDENT COMMA t = ty RPAREN
    { ParseTypes.Ref(id,t) }
%public ty: t = annotated(ty_nopos) { t }

product_ty:
  | t1 = stype STAR t2 = stype { [t1;t2] }
  | t1 = stype STAR tl = product_ty { t1 :: tl }
