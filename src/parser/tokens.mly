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

%token <Big_int.big_int> INT
%token RPAREN LCURL SECTION BEGIN END DLBRACKET DRBRACKET LBRACKET RBRACKET
(* %token DLCURL DRCURL *)
%token <string> STRING IDENT TYVAR CONSTRUCTOR
%token IN SEMICOLON COQ TAKEOVER PANGOLINE LE LT BLE BLT BGT BGE
%token PLUS MINUS EQUAL STAR NEQ BEQUAL BNEQ ARROW COMMA AND OR GE GT
%token ASSIGN REF LETREGION TILDE UNDERSCORE PREDEFINED LPAREN
%token MATCH WITH TO DOWNTO FOR DONE EOF
%token REC PTRUE PFALSE TINT PROP DEXCLAM VOID
%token EXCLAM IF FUN LET AXIOM RCURL
%token LOGIC TYPE FORALL EXISTS PARAMETER GOAL LEMMA
%token COLON MID AT THEN ELSE DOT DO INDUCTIVE OF

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

