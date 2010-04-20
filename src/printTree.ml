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

module SS = Misc.StringSet

type effect = string list * string list
type rw = effect * effect
type ty =
  | TConst of Const.ty
  | Tuple of ty list
  | Arrow of ty * ty * rw
  | PureArr of ty * ty
  | TApp of string * ty list
  | Ref of string * ty
  | Map of effect

type inst = ty list * string list * effect list
type gen = string list * string list * string list
type scheme = gen * ty

type t =
  | Const of Const.t
  | Var of string * inst * ty * [`Infix | `Prefix ]
  | Get of t * t
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t
  | Lam of string * ty * funcbody
  | Let of gen * t * string * t * isrec
  | PureFun of string * ty * t
  | Ite of t * t * t
  | Quant of [`FA | `EX ] * string * ty * t
  | Param of ty * rw
  | Gen of gen *  t
  | PRef of string
  | HoareTriple of funcbody
  | LetReg of string list * t
  | Case of t * branch list
and funcbody = t * t * t
and isrec = ty Const.isrec
and branch = pattern * t
and pattern =
  | PVar of string
  | PApp of string * inst * pattern list

type decl =
  | Logic of string * scheme
  | Formula of string * t * [ `Proved | `Assumed ]
  | Section of string * decl list * section_kind
  | TypeDef of string * string list * typedef
  | Inductive of string * gen * ty list * inductive_branch list
  | Program of string * gen * t * isrec
  | DLetReg of string list
  | DGen of gen
  | Decl of string
and typedef =
  | Abstract
  | ADT of constbranch list
and constbranch = string * ty list
and inductive_branch = string * t

and section_kind = [ `Block of Const.takeover list | `Structure ]

module Generic = struct
  open Myformat
  let effect_no_sep fmt (r,e) =
      fprintf fmt "%a %a" (list space string) r
        (list space string) (List.map (fun s -> "'" ^ s) e)

  let effect fmt e = fprintf fmt "{%a}" effect_no_sep e

  let rw_nosep fmt (e1,e2) =
    fprintf fmt "%a + %a" effect_no_sep e1 effect_no_sep e2

  let rw fmt rw = fprintf fmt "{%a}" rw_nosep rw

  let eff_empty = [], []
  let rw_empty = eff_empty, eff_empty

  let split t =
    match t with
    | PureArr (t1,t2) -> t1, None, t2
    | Arrow (t1,t2,eff) -> t1, Some eff, t2
    | _ -> raise Exit

  let nsplit =
    let rec aux (tl,eff) t =
      try
        let t1,eff', t2 = split t in
        match eff' with
        | None -> aux (t1::tl,None) t2
        | Some _ -> List.rev tl, eff', t2
      with Exit -> List.rev tl, eff, t in
    aux ([],None)

  let lambdadestruct =
    let rec aux acc t =
      match t with
      | PureFun (x,t,e) -> aux ((x,t)::acc) e
      | Lam (x,t,(p,e,q)) -> List.rev ((x,t)::acc), p, e, q
      | _ -> assert false in
    aux []

  let is_compound kind = function
    | TConst _ | Ref _ | Map _ -> false
    | TApp (_,_ :: _) -> kind = `Coq
    | TApp _ -> false
    | Tuple _ | Arrow _ | PureArr _ -> true

  let is_empty (l1,l2,l3) = l1 = [] && l2 = [] && l3 = []

  let prl pr = list comma pr
  let prsl pr fmt l =
    if l = [] then () else
      fprintf fmt "@ %a" (list space pr) l

  let tyvar fmt x = fprintf fmt "'%a" string x
  let gen fmt ((tl,rl,el) as g) =
    if is_empty g then ()
    else fprintf fmt "[%a|%a|%a]" (list space tyvar) tl
      (list space string) rl (list space tyvar) el

  let lname s fmt l =
    if l = [] then () else
    fprintf fmt "(%a :@ %s)" (list space string) l s

  let is_compound_term = function
    | Const _ | Var _ | Lam _ | PureFun _ | Get _ | PRef _ -> false
    | App _ | Let _ | Ite _ | Case _
    | Quant _ | Param _ | LetReg _ | Gen _ | HoareTriple _ -> true

  let inductive_sep fmt () = fprintf fmt "@ |@ "
  let consttysep fmt () = fprintf fmt "*@ "

end

module Coq = struct
  open Myformat
  open Generic

(*
  let needs_inst t =
    match t with
    | TApp _ | Tuple _ -> true
    | _ -> false

*)
  let rec inst fmt (tl,_,_) = fprintf fmt "%a" (prsl mayp) tl
  and ty fmt x =
    match x with
    | Arrow _ | Map _ | Ref _ -> assert false
    | PureArr (t1,t2) -> fprintf fmt "%a ->@ %a" mayp t1 ty t2
    | Tuple tl -> list (fun fmt () -> fprintf fmt " *@ ") mayp fmt tl
    | TConst c -> Const.print_ty `Coq fmt c
    | TApp (v,[]) -> fprintf fmt "%a" string v
    | TApp (v,i) -> fprintf fmt "%a %a" string v (list space mayp) i
  and mayp fmt t =
    if is_compound `Coq t then paren ty fmt t else ty fmt t

  let binder' par =
    let p fmt (x,t) = fprintf fmt "%a:%a" string x ty t in
    if par then paren p else p
  let binder fmt b = binder' true fmt b

  let rec term fmt x =
    match x with
    | Const c -> Const.print `Coq fmt c
    | App (App (Var(v,_,_,`Infix),t1),t2) ->
        fprintf fmt "@[%a@ %a@ %a@]" with_paren t1 string v with_paren t2
    | App (t1,t2) ->
          fprintf fmt "@[%a@ %a@]" term t1 with_paren t2
    | Ite (e1,e2,e3) ->
        fprintf fmt "@[if %a then@ %a else@ %a@]" term e1 term e2 term e3
    | PureFun (x,t,e) ->
        fprintf fmt "@[(fun %a@ =>@ %a)@]" binder (x,t) term e
    | Let (g,e1,x,e2,_) ->
        fprintf fmt "@[let@ %a %a=@[@ %a@]@ in@ %a@]" string x gen g
          term e1 term e2
    | Var (v,i,_,_) ->
        if not (is_empty i) then
          fprintf fmt "(@@%a %a)" string v inst i
        else string fmt v
    | Quant (k,x,t,e) ->
        let bind = if k = `FA then binder else binder' false in
        fprintf fmt "@[%a %a,@ %a@]" Const.quant k bind (x,t) term e
    | Case (t,bl) ->
        fprintf fmt "@[match %a with @[%a@] end @]" term t
          (list inductive_sep branch) bl
    | Gen ((tl,_,_),t) ->
        if tl = [] then term fmt t else
          fprintf fmt "%a %a" pr_generalize tl term t
    (* specific to Who, will not be printed in backends *)
    | Param _ | HoareTriple _ | LetReg _ | Lam _ | Get _ | PRef _ ->
        assert false
  and with_paren fmt x =
    if is_compound_term x then paren term fmt x else term fmt x
  and branch fmt (p,t) =
    fprintf fmt "%a@ =>@ @[ %a @]" pattern p term t
  and pattern fmt p =
    match p with
    | PVar v -> string fmt v
    | PApp (v,_,pl) ->
        if pl = [] then string fmt v
        else fprintf fmt "%a %a" string v (list space mayparen_pattern) pl
  and mayparen_pattern fmt p =
    match p with
    | PVar _ -> pattern fmt p
    | _ -> paren pattern fmt p
  and pr_generalize fmt tl =
    if tl = [] then ()
    else fprintf fmt "forall@ %a@ ,@ " (lname "Type") tl

  let def fmt insection =
    if insection then string fmt "Variable" else string fmt "Definition"

  let print_proof fmt = fprintf fmt "@\nProof.@\nAdmitted.@\n"

  let print_def_end fmt insection =
    if not insection then print_proof fmt

  let intro_name s fmt l =
    if l = [] then () else
    fprintf fmt "Variables %a :@ %s.@ " (list space string) l s

  let arrow fmt () = string fmt "->@ "
  let rec decl insection fmt d =
    match d with
    | Logic (x,((tl,_,_),t)) ->
          fprintf fmt "@[<hov 2>%a %a:@ %a %a.%a @]"
            def insection string x pr_generalize tl ty t print_def_end insection
    | Formula (s,t,`Assumed) ->
        fprintf fmt "@[<hov 2>Hypothesis %a:@ %a. @]" string s term t
    | Formula (s,t,`Proved) ->
        fprintf fmt "@[<hov 2>Lemma %a:@ %a. %t@]" string s term t print_proof
    | TypeDef (x,tl, Abstract) ->
        fprintf fmt "@[<hov 2>Definition %a :@ %a%s. %t @]" string x
          pr_generalize tl "Type" print_proof
    | TypeDef (n,tl,ADT bl) ->
        fprintf fmt "@[<hov 2>Inductive %a %a : Type := | %a . @]"
          string n (lname "Type") tl (list inductive_sep (constdef n tl)) bl
    | Inductive (n,g,tyl, fl) ->
        fprintf fmt "@[<hov 2>Inductive %a %a : %a -> Prop := %a.@]"
          string n inductive_intros g
          (list arrow mayp) tyl (list space ind_term) fl
    | Section (_,d, `Block cl) ->
        let choice = List.fold_left (fun acc (p,c) ->
          if p = `Coq then c else acc) Const.TakeOver cl in
        begin match choice with
        | Const.Predefined -> ()
        | Const.Include f -> fprintf fmt "Require Import %s." f
        | Const.TakeOver -> theory insection fmt d
        end
    | Section (s,d, `Structure) ->
        fprintf fmt "@[<hov 2>Section %s. @\n %a@] End %s." s (theory true) d s
    | DLetReg _ -> assert false
    | Program (x,g,t,_) ->
        fprintf fmt "@[<hov 2>let@ %a %a = %a @]" string x gen g term t
    | DGen (tl,_,_) -> intro_name "Type" fmt tl
    | Decl s -> string fmt s
  and constdef n tvl fmt (c,tl) =
    if tl = [] then fprintf fmt "%a : %a %a " string c string n
      (list space string) tvl
    else fprintf fmt "%a : %a -> %a %a" string c (list arrow ty) tl string n
      (list space string) tvl
  and theory insection fmt t = list newline (decl insection) fmt t
  and arrow fmt () = fprintf fmt "->@ "
  and inductive_intros fmt (tl,_,_) =
    fprintf fmt "( %a : Type)" (list space string) tl
  and ind_term fmt (s,t) = fprintf fmt "| %s : %a" s term t

end

module Pangoline = struct
  open Myformat
  open Generic

  let rec inst fmt (tl,_,_) =
    if tl = [] then () else fprintf fmt "[%a]" (prl ty) tl
  and ty fmt x =
    match x with
    | Arrow _ | Map _ | Ref _ -> assert false
    | PureArr (t1,t2) -> fprintf fmt "%a ->@ %a" mayp t1 ty t2
    | Tuple tl -> list (fun fmt () -> fprintf fmt " *@ ") mayp fmt tl
    | TConst c -> Const.print_ty `Pangoline fmt c
    | TApp (v,[]) -> fprintf fmt "%a" string v
    | TApp (v,i) -> fprintf  fmt "%a[%a]" string v (list comma mayp) i
  and mayp fmt t =
      if is_compound `Pangoline t then paren ty fmt t else ty fmt t

  let binder' par =
    let p fmt (x,t) = fprintf fmt "%a:%a" string x ty t in
    if par then paren p else p
  let binder fmt b = binder' true fmt b

  let rec term fmt t =
    match t with
    | Const c -> Const.print `Pangoline fmt c
    | App (App (Var(v,i,_,`Infix),t1),t2) ->
        fprintf fmt "@[%a@ %a%a@ %a@]" with_paren t1 string v inst i
          with_paren t2
    | App (t1,t2) ->
          fprintf fmt "@[%a@ %a@]" term t1 with_paren t2
    | Ite (e1,e2,e3) ->
        fprintf fmt "@[if %a then@ %a else@ %a@]" term e1 term e2 term e3
    | PureFun (x,t,e) ->
        fprintf fmt "@[(fun %a@ ->@ %a)@]" binder (x,t) term e
    | Let (g,e1,x,e2,_) ->
        fprintf fmt "@[let@ %a %a=@[@ %a@]@ in@ %a@]" string x gen g
          term e1 term e2
    | Var (v,i,_,_) ->
        let pr fmt () =
          if is_empty i then string fmt v
          else fprintf fmt "%a %a" string v inst i in
        if Identifiers.is_infix_id v then paren pr fmt () else pr fmt ()
    | Quant (k,x,t,e) ->
        fprintf fmt "@[%a %a.@ %a@]" Const.quant k binder (x,t) term e
    | Gen ((tl,_,_) as g,t) ->
        if is_empty g then term fmt t else
          fprintf fmt "forall type %a. %a" (list space string) tl term t
    | Case (t,bl) ->
        fprintf fmt "@[case %a of @[%a@] end @]" term t
          (list inductive_sep branch) bl
    (* specific to Who, will not be printed in backends *)
    | Param _ | HoareTriple _ | LetReg _ | Lam _ | Get _ | PRef _ ->
        assert false
  and with_paren fmt x =
    if is_compound_term x then paren term fmt x else term fmt x
  and branch fmt (p,t) =
    fprintf fmt "%a@ ->@ @[ %a @]" pattern p term t
  and pattern fmt p =
    match p with
    | PVar v -> string fmt v
    | PApp (v,_,pl) ->
        if pl = [] then fprintf fmt "%a" string v
        else fprintf fmt "%a(%a)" string v (list comma pattern) pl

  let pr_generalize in_term fmt tl =
    if tl = [] then ()
    else
      let in_term fmt = if in_term then string fmt "type" else () in
      fprintf fmt "forall %t %a." in_term (list space string) tl

  let is_infix_symbol s =
    match s.[0] with
    | '=' | '!' | '+' | '-' | '*' | '<' | '>'  -> true
    | _ -> false

  let rec decl fmt d =
    match d with
    | Logic (x,((tl,_,_),t)) ->
        if is_infix_symbol x then
          fprintf fmt "infix %a %d@\n" string x 0;
          let npr fmt n =
            if is_infix_symbol n
            then fprintf fmt "( %a )" string n
            else string fmt n in
          fprintf fmt "@[<hov 2>logic %a:@ %a %a@]"
            npr x (pr_generalize false) tl ty t
    | Formula (s,t,`Assumed) ->
        fprintf fmt "@[<hov 2>hypothesis %a:@ %a @]" string s term t
    | Formula (s,t,`Proved) ->
        fprintf fmt "@[<hov 2>lemma %a:@ %a@]" string s term t
    | TypeDef (x,tl, Abstract) ->
        fprintf fmt "@[<hov 2> type (%d) %a @]" (List.length tl) string x
    | TypeDef (n,tl,ADT bl) ->
        if tl = [] then
          fprintf fmt "@[<hov 2>type %a = | %a @]" string n
            (list inductive_sep constdef) bl
        else
          fprintf fmt "@[<hov 2>type %a %a = | %a @]"
            (paren (list comma string)) tl string n
            (list inductive_sep constdef) bl
    | Inductive (n,g,tyl, fl) ->
        fprintf fmt "@[<hov 2>inductive %a %a %a = %a@]" string n gen g
          (list space ty) tyl (list inductive_sep induct_branch) fl
    | DLetReg _ -> assert false
    | Section (_,d, `Block cl) ->
        let choice = List.fold_left (fun acc (p,c) ->
          if p = `Pangoline then c else acc) Const.TakeOver cl in
        begin match choice with
        | Const.Predefined -> ()
        | Const.Include f -> fprintf fmt "Require Import %s." f
        | Const.TakeOver -> theory fmt d
        end
    | Section (_,d, `Structure) ->
        fprintf fmt "@[<hov 2>begin @\n %a@] end" theory d
    | Program (x,_,t,_) ->
        fprintf fmt "@[<hov 2>definition@ %a = %a @]" string x term t
    | DGen (tl,_,_) ->
        list newline (fun fmt s -> fprintf fmt "type (0) %a" string s) fmt tl
    | Decl s -> string fmt s
  and constdef fmt (c,tl) =
    if tl = [] then string fmt c
    else fprintf fmt "%a of %a" string c (list consttysep ty) tl
  and theory fmt t = list newline decl fmt t
  and induct_branch fmt (_,t) = term fmt t
end

module Who = struct
  open Myformat
  open Generic

  let rec ty fmt x =
    match x with
      | Arrow (t1,t2,eff) ->
          fprintf fmt "%a ->%a %a" mayp t1 rw eff ty t2
      | Map e -> fprintf fmt "<%a>" effect_no_sep e
      | PureArr (t1,t2) -> fprintf fmt "%a ->@ %a" mayp t1 ty t2
      | Tuple tl -> list (fun fmt () -> fprintf fmt " *@ ") mayp fmt tl
      | TConst c -> Const.print_ty `Who fmt c
      | Ref (r,t) -> fprintf fmt "ref(%a,%a)" string r ty t
      | TApp (v,[]) -> fprintf fmt "%a" string v
      | TApp (v,i) -> fprintf  fmt "%a[%a]" string v (list comma ty) i
  and mayp fmt t =
      if is_compound `Who t then paren ty fmt t else ty fmt t

  let binder' par =
    let p fmt (x,t) = fprintf fmt "%a:%a" string x ty t in
    if par then paren p else p
  let binder fmt b = binder' true fmt b

  let inst fmt ((tl,rl,el) as g) =
    (* separate types with comma, the others by spaces *)
    if is_empty g then () else
    fprintf fmt "[%a|%a|%a]" (prl ty) tl (prsl string) rl (prsl effect) el

  let prrec fmt = function
    | Const.NoRec -> ()
    | Const.Rec t -> fprintf fmt "rec(%a) " ty t
    | Const.LogicDef -> fprintf fmt "logic "

  let rec term fmt t =
    match t with
    | Const c -> Const.print `Who fmt c
    | App (App (Var(v,_,_,`Infix),t1),t2) ->
        fprintf fmt "@[%a@ %a@ %a@]" with_paren t1 string v with_paren t2
    | App (t1,t2) ->
          fprintf fmt "@[%a@ %a@]" term t1 with_paren t2
    | Ite (e1,e2,e3) ->
        fprintf fmt "@[if %a then@ %a else@ %a@]" term e1 term e2 term e3
    | PureFun (x,t,e) ->
        fprintf fmt "@[(fun %a@ ->@ %a)@]" binder (x,t) term e
    | Let (g,e1,x,e2,r) ->
        fprintf fmt "@[let@ %a%a %a=@[@ %a@]@ in@ %a@]"
          prrec r string x gen g term e1 term e2
    | Var (v,i,_,_) ->
        let pr fmt () =
          if is_empty i then string fmt v
          else fprintf fmt "%a %a" string v inst i
        in
        if Identifiers.is_infix_id v then paren pr fmt () else pr fmt ()
    | Quant (k,x,t,e) ->
        fprintf fmt "@[%a %a.@ %a@]" Const.quant k binder (x,t) term e
    | Gen (g,t) ->
        if is_empty g then term fmt t else
          fprintf fmt "forall %a. %a" gen g term t
    | Param (t,e) ->
        fprintf fmt "parameter(%a,%a)" ty t rw e
    | HoareTriple (p,f,q) ->
        fprintf fmt "[[%a]]%a[[%a]]" term p term f term q
    | LetReg (v,t) ->
        fprintf fmt "@[letregion %a in@ %a@]"
          (list space string) v term t
    | Lam (x,t,(p,e,q)) ->
        fprintf fmt "@[(fun %a@ ->@ {%a}@ %a@ {%a})@]"
          binder (x,t) term p term e term q
    | Case (t,bl) ->
        fprintf fmt "@[match %a with @[%a@] end @]" term t
          (list inductive_sep branch) bl
    | Get (r,t) -> fprintf fmt "!!%a@@%a" term r term t
    | PRef r -> fprintf fmt "ref(%a)" string r
  and with_paren fmt x =
    if is_compound_term x then paren term fmt x else term fmt x
  and branch fmt (p,t) =
    fprintf fmt "%a@ ->@ @[ %a @]" pattern p term t
  and pattern fmt p =
    match p with
    | PVar v -> string fmt v
    | PApp (v,_,pl) ->
        if pl = [] then string fmt v
        else fprintf fmt "%a(%a)" string v (list comma pattern) pl


  let rec decl fmt d =
    match d with
    | Logic (x,(g,t)) ->
        fprintf fmt "@[<hov 2>logic %a %a : %a@]" string x gen g ty t
    | Formula (s,t,`Assumed) ->
        fprintf fmt "@[<hov 2>axiom %a:@ %a @]" string s term t
    | Formula (s,t,`Proved) ->
        fprintf fmt "@[<hov 2>goal %a:@ %a@]" string s term t
    | TypeDef (x,tl, Abstract) ->
        fprintf fmt "@[type %a%a@]" string x gen (tl,[],[])
    | Inductive (n,g,tyl, fl) ->
        fprintf fmt "@[<hov 2>inductive %a %a %a = %a end@]" string n gen g
          (list comma ty) tyl (list inductive_sep induct_branch) fl
    | TypeDef (n,tl,ADT bl) ->
        fprintf fmt "@[<hov 2>type %a %a = | %a @]"
          string n gen (tl,[],[]) (list inductive_sep constdef) bl
    | DLetReg l ->
        fprintf fmt "@[letregion %a@]" (list space string) l
    | Section (_,d, `Block cl) ->
        let choice = List.fold_left (fun acc (p,c) ->
          if p = `Who then c else acc) Const.TakeOver cl in
        begin match choice with
        | Const.Predefined -> ()
        | Const.Include f -> fprintf fmt "Require Import %s." f
        | Const.TakeOver -> theory fmt d
        end
    | Section (s,d, `Structure) ->
        fprintf fmt "@[<hov 2>section %s @\n %a@] end" s theory d
    | Program (x,g,t,r) ->
        begin match r with
        | Const.NoRec | Const.LogicDef ->
            fprintf fmt "@[<hov 2>let@ %a %a = %a @]" string x gen g term t
        | Const.Rec recty ->
            let _,eff,rt = nsplit recty in
            let eff = match eff with None -> rw_empty | Some eff -> eff in
            let args, p,e,q = lambdadestruct t in
            fprintf fmt
              "@[<hov 2>let rec@ %a@ %a@ %a@ :@ %a %a = {%a}@ %a@ {%a} @]"
              string x gen g arglist args ty rt rw eff term p term e term q
        end
    | DGen g -> fprintf fmt "@[INTROS %a@]" gen g
    | Decl s -> string fmt s
  and constdef fmt (c,tl) =
    if tl = [] then string fmt c
    else fprintf fmt "%a of %a" string c (list consttysep ty) tl
  and theory fmt t = list newline decl fmt t
  and arglist fmt l = list space arg fmt l
  and arg fmt (x,t) = fprintf fmt "(%a : %a)" string x ty t
  and induct_branch fmt (_,t) = term fmt t

end

module Print = struct
  open Myformat
  include Generic

  let inst ?(kind=`Who) =
    match kind with
    | `Who -> Who.inst
    | `Coq -> Coq.inst
    | `Pangoline -> Pangoline.inst

  let ty ?(kind=`Who) =
    match kind with
    | `Who -> Who.ty
    | `Coq -> Coq.ty
    | `Pangoline -> Pangoline.ty

  let varprint kind fmt x =
    match kind with
    | `Who -> fprintf fmt "'%a" string x
    | `Coq | `Pangoline -> string fmt x
  let varlist = list space (varprint `Who)

  let scheme fmt (g,t) = fprintf fmt "forall %a. %a" gen g (ty ~kind:`Who) t

  let term ?(kind=`Who) =
    match kind with
    | `Who -> Who.term
    | `Coq -> Coq.term
    | `Pangoline -> Pangoline.term

  let decl ?(kind = `Who) =
    match kind with
    | `Who -> Who.decl
    | `Coq -> Coq.decl false
    | `Pangoline -> Pangoline.decl

  let theory ?(kind=`Who) fmt t =
    let t =
      match kind with
      | `Coq -> Decl "Set Implicit Arguments." :: t
      | _ -> t in
    match kind with
    | `Who -> Who.theory fmt t
    | `Coq -> Coq.theory false fmt t
    | `Pangoline -> Pangoline.theory fmt t

end
