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

type ('a,'b,'c) t' = 
  | Const of Const.ty
  | Tuple of 'a * 'a
  | Arrow of 'a * 'a * 'c * 'b list
  | PureArr of 'a * 'a
  | App of Name.t * ('a,'b,'c) Inst.t
  | Ref of 'b * 'a
  | Map of 'c
type t = C of (t,Name.t,Effect.t) t'

val print : t Myformat.fmt
val print_list : 
  unit Myformat.fmt -> t list Myformat.fmt
val print' : ?kind:[`Coq | `Who | `Pangoline ] -> 'a Myformat.fmt -> 
  'b Myformat.fmt -> 'c Myformat.fmt -> ('a -> bool) -> 
    (('a ,'b,'c) t') Myformat.fmt

val varprint : [`Coq | `Who | `Pangoline ] -> Name.t Myformat.fmt

val is_compound : ('a,'b,'c) t' -> bool

val coq_print : t Myformat.fmt

val gen_print : [`Coq | `Who | `Pangoline ] -> t Myformat.fmt

val is_compound : ('a,'b,'c) t' -> bool
val var : Name.t -> t
val const : Const.ty -> t
val arrow : t -> t -> Effect.t -> t
val caparrow : t -> t -> Effect.t -> Name.t list -> t
val parr : t -> t -> t
val tuple : t -> t -> t
val ref_ : Name.t -> t -> t
val map : Effect.t -> t
val unit : t
val prop : t
val bool : t
val int : t
val emptymap : t

val arg : t -> t
val result : t -> t
val split : t -> t * t
val latent_effect : t -> Effect.t
val domain : t -> Effect.t
val is_map : t -> bool
val is_ref : t -> bool
val destr_tuple : t -> t * t

val to_logic_type : t -> t
val from_logic_tuple : t -> t * t * Effect.t

val tlsubst : Name.t list -> t list -> t -> t
val rlsubst : Name.t list -> Name.t list -> t -> t
val elsubst : Name.t list -> Effect.t list -> t -> t
val rsubst : Name.t list -> Name.t list -> Name.t -> Name.t
val app : Name.t -> (t,Name.t,Effect.t) Inst.t -> t

val equal : t -> t -> bool

module Generalize : sig
  type t = Name.t list * Name.t list * Name.t list
  type 'a bind = 'a Name.listbind Name.listbind Name.listbind

  val empty : t 
  val is_empty : t -> bool

  val print : t Myformat.fmt
  val open_ : (Name.subst -> 'a -> 'a) -> 'a bind -> t * 'a
  val sopen_ : 'a bind -> t * 'a
  val close : t -> 'a -> 'a bind 

  val equal : t -> t -> bool

  val get_first : t -> Name.t
end

val allsubst : 
  Generalize.t -> t list * Name.t list * Effect.t list -> 
    t -> t

val forty : Generalize.t * t

val find_type_of_r : Name.t -> t -> t option

val get_reg : t -> Name.t

val selim_map : (Name.t -> t) -> t -> t

val pretype : t -> Effect.t -> t
val posttype : t -> t -> Effect.t -> t
val prepost_type: t -> t -> Effect.t -> t

module Predef : sig
  val prop_2 : t
  val prop_3 : t
  val bool_3 : t
  val int_3 : t
  val iip : t
  val iib : t
  val aap : Generalize.t * t
  val aab : Generalize.t * t
  val mk_tuple : Generalize.t * t

  val fst : Generalize.t * t
  val snd : Generalize.t * t
  
  val combine : Generalize.t * t
  val restrict : Generalize.t * t
  val get : Generalize.t * t
end
