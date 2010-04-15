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

%token <Big_int.big_int Loc.t> INT
%token <Loc.loc> LPAREN RPAREN LCURL SECTION END
%token DLCURL DRCURL PREDEFINED
%token <string Loc.t> IDENT TYVAR
%token <string> STRING
%token IN SEMICOLON COQ ALLOCATES TAKEOVER PANGOLINE
%token <Loc.loc> PLUS MINUS EQUAL STAR NEQ BEQUAL BNEQ ARROW COMMA AND OR
%token <Loc.loc> ASSIGN GE GT LE LT REF LETREGION TILDE UNDERSCORE
%token <Loc.loc> BLE BLT BGT BGE DLBRACKET DRBRACKET LBRACKET RBRACKET
%token EOF
%token REC
%token <Loc.loc> EXCLAM DEXCLAM IF FUN PTRUE PFALSE VOID LET AXIOM RCURL TINT
%token <Loc.loc> LOGIC TYPE FORALL EXISTS PARAMETER TO DOWNTO FOR DONE GOAL PROP
%token COLON MID AT THEN ELSE DOT DO INTROS INDUCTIVE OF

%nonassoc below_SEMI
%nonassoc SEMICOLON
%nonassoc ELSE
%nonassoc below_COMMA
%left     COMMA
%nonassoc forall
%right ARROW
%left AND OR
%nonassoc LE LT GE GT BLE BLT BGT BGE
%nonassoc ASSIGN
%right EQUAL NEQ BEQUAL BNEQ
%left PLUS MINUS
%right STAR

%%

