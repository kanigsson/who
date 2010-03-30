module SS = Misc.StringSet

type effect = string list * string list
type ty =
  | TConst of Const.ty
  | Tuple of ty list
  | Arrow of ty * ty * effect * string list
  | PureArr of ty * ty
  | TApp of string * inst
  | Ref of string * ty
  | Map of effect

and inst = ty list * string list * effect list
type gen = string list * string list * string list
type scheme = gen * ty

type t =
  | Const of Const.t
  | Var of string * inst
  (* app (f,x,_,r) - r is the list of region names this execution creates -
  obligatory *)
  | App of t * t * [`Infix | `Prefix ] * string list
  | Lam of string * ty * string list * funcbody
  | Let of gen * t * string * t * isrec
  | PureFun of string * ty * t
  | Ite of t * t * t
  | Quant of [`FA | `EX ] * string * ty * t
  | Param of ty * effect
  | Gen of gen *  t
  | HoareTriple of funcbody
  | LetReg of string list * t
and funcbody = t * t * t
and isrec = ty Const.isrec

type decl = 
  | Logic of string * scheme
  | Formula of string * t * [ `Proved | `Assumed ]
  | Section of string * Const.takeover list * decl list
  | TypeDef of gen * ty option * string
  | Program of string * gen * t * isrec
  | DLetReg of string list
  | DGen of gen

module Print = struct
  open Myformat

  let effect_no_sep fmt (r,e) =
      fprintf fmt "%a %a" (list space string) r
        (list space string) (List.map (fun s -> "'" ^ s) e)

  let effect fmt e = fprintf fmt "{%a}" effect_no_sep e


  let is_compound = function
    | TConst _ | Ref _ | Map _ | TApp _ -> false
    | Tuple _ | Arrow _ | PureArr _ -> true

  let maycap pr fmt = function
    | [] -> ()
    | l -> fprintf fmt "|%a" (list space pr) l

  let is_empty (l1,l2,l3) = l1 = [] && l2 = [] && l3 = []

  let prl pr = list comma pr
  let prsl pr fmt l =
    if l = [] then () else
      fprintf fmt "@ %a" (list space pr) l

  let rec inst ?(kind=`Who) ~intype fmt ((tl,rl,el) as g) =
    if is_empty g then () else
      match kind with
      | `Who ->
          (* separate types with comma, the others by spaces *)
          fprintf fmt "[%a|%a|%a]" (prl (ty ~kind)) tl
            (prsl string) rl (prsl effect) el
      | `Coq ->
          if intype then
            fprintf fmt "%a%a%a" (prsl (ty ~kind)) tl (prsl string) rl
              (prsl effect) el
      | `Pangoline ->
          if tl = [] then () else fprintf fmt "[%a]" (prl (ty ~kind)) tl


  and ty ?(kind=`Who) =
    let rec print fmt x =
      match x with
      | Arrow (t1,t2,eff,cap) ->
          (* there are no impure arrow types in Coq or Pangoline, so simply
           * print it as you wish *)
          fprintf fmt "%a ->{%a%a} %a" mayp t1
          effect_no_sep eff (maycap string) cap print t2
      | Map e -> fprintf fmt "<%a>" effect_no_sep e
      | PureArr (t1,t2) -> fprintf fmt "%a ->@ %a" mayp t1 print t2
      | Tuple tl ->
          list (fun fmt () -> fprintf fmt " *@ ") mayp fmt tl
      | TConst c -> Const.print_ty kind fmt c
      | Ref (r,t) ->
          (* in Who, this is a special type constructor, in Coq its a simple
          application, in Pangoline its a type instantiation *)
          begin match kind with
          | `Who -> fprintf fmt "ref(%a,%a)" string r print t
          | `Coq -> fprintf fmt "ref@ %a@ %a" mayp t string r
          | `Pangoline -> fprintf fmt "%a ref" mayp t
          end
      | TApp (v,i) -> fprintf fmt "%a%a" string v (inst ~kind ~intype:true) i
    and mayp fmt t = if is_compound t then paren print fmt t else print fmt t in
    print

  let varprint kind fmt x =
    match kind with
    | `Who -> fprintf fmt "'%a" string x
    | `Coq | `Pangoline -> string fmt x
  let varlist = list space (varprint `Who)

  let gen fmt ((tl,rl,el) as g) =
    if is_empty g then ()
    else fprintf fmt "[%a|%a|%a]" varlist tl (list space string) rl varlist el

  let scheme fmt (g,t) = fprintf fmt "forall %a. %a" gen g (ty ~kind:`Who) t

  let is_compound = function
    | Const _ | Var _ | Lam _ | PureFun _ -> false
    | App _ | Let _ | Ite _
    | Quant _ | Param _ | LetReg _ | Gen _ | HoareTriple _ -> true

  type sup = [ `Coq | `Who | `Pangoline ]

  let maycaplist fmt l =
    if l = [] then ()
    else fprintf fmt "allocates %a" (list space string) l

  let prrec fmt = function
    | Const.NoRec -> ()
    | Const.Rec t -> fprintf fmt "rec(%a) " (ty ~kind:`Who) t
    | Const.LogicDef -> fprintf fmt "logic "

  let lname s fmt l =
    if l = [] then () else
    fprintf fmt "(%a :@ %s)" (list space string) l s

  let is_compound = function
    | Const _ | Var _ | Lam _ | PureFun _ -> false
    | App _ | Let _ | Ite _
    | Quant _ | Param _ | LetReg _ | Gen _ | HoareTriple _ -> true

  let term ?(kind : sup =`Who) =
    let ty = ty ~kind in
    let rec print fmt x =
      match x with
      | Const c -> Const.print fmt c
      | App (App (Var(v,i),t1,_,_),t2,`Infix,_) ->
          fprintf fmt "@[%a@ %a%a@ %a@]" with_paren t1 string v inst' i
            with_paren t2
      | App (t1,t2,_,cap) ->
            fprintf fmt "@[%a%a@ %a@]" print t1 maycap cap with_paren t2
      | Ite (e1,e2,e3) ->
          fprintf fmt "@[if %a then@ %a else@ %a@]" print e1 print e2 print e3
      | PureFun (x,t,e) ->
          fprintf fmt "@[(fun %a@ %a@ %a)@]" binder (x,t)
            Const.funsep kind print e
      | Let (g,e1,x,e2,r) ->
          fprintf fmt "@[let@ %a%a %a=@[@ %a@]@ in@ %a@]"
            prrec r string x gen g print e1 print e2
      | Var (v,i) ->
          begin match kind with
          | `Who | `Pangoline ->
              let pr fmt () =
                if is_empty i then string fmt v
                else fprintf fmt "%a %a" string v inst' i
              in
              if Identifiers.is_infix_id v then paren pr fmt () else pr fmt ()
          | `Coq -> string fmt v
          end
      | Quant (k,x,t,e) ->
          let bind = if k = `FA then binder else binder' false in
          fprintf fmt "@[%a %a%a@ %a@]" Const.quant k bind (x,t)
            Const.quantsep kind print e
      | Gen ((tl,_,_) as g,t) ->
          if is_empty g then print fmt t else
            begin match kind with
            | `Coq ->
                fprintf fmt "forall@ %a,@ %a " (lname "Type") tl print t
            | `Pangoline  ->
                fprintf fmt "forall type %a. %a" (list space string) tl print t
            | `Who ->
                fprintf fmt "forall %a%a %a" gen g Const.quantsep kind print t
            end
      (* specific to Who, will not be printed in backends *)
      | Param (t,e) ->
          fprintf fmt "parameter(%a,%a)" ty t effect e
      | HoareTriple (p,f,q) ->
          fprintf fmt "[[%a]]%a[[%a]]" print p print f print q
      | LetReg (v,t) ->
          fprintf fmt "@[letregion %a in@ %a@]"
            (list space string) v print t
      | Lam (x,t,cap,(p,e,q)) ->
          fprintf fmt "@[(fun %a@ ->%a@ {%a}@ %a@ {%a})@]"
            binder (x,t) maycaplist cap print p print e print q
    and binder' par =
      let p fmt (x,t) = fprintf fmt "%a:%a" string x ty t in
      if par then paren p else p
    and binder fmt b = binder' true fmt b
    and maycap fmt = function
      | [] -> ()
      | l -> fprintf fmt "{%a}" (list space string) l
    and with_paren fmt x =
      if is_compound x then paren print fmt x else print fmt x
    and inst' fmt i = inst ~kind ~intype:false fmt i in
    print


  let decl ?(kind=`Who) =
    let ty = ty ~kind in
    let term = term ~kind in
    let rec decl fmt d =
      match d with
      | Logic (x,(g,t)) ->
          fprintf fmt "@[<hov 2>logic %a %a : %a@]"
            string x gen g ty t
      | Formula (s,t,`Assumed) ->
          fprintf fmt "@[<hov 2>axiom %s : %a@]" s term t
      | Formula (s,t,`Proved) ->
          fprintf fmt "@[<hov 2>goal %s : %a@]" s term t
      | TypeDef (g,t,x) ->
          begin match t with
          | None -> fprintf fmt "@[type %a%a@]" string x gen g
          | Some t ->
              fprintf fmt "@[<hov 2>type %a%a =@ %a@]" string x gen g ty t
          end
      | DLetReg l ->
          fprintf fmt "@[letregion %a@]" (list space string) l
      | Section (s,cl,d) ->
          fprintf fmt "@[<hov 2>section %s@, %a@, %a@] end" s
          (list newline Const.takeover) cl theory d
      | Program (x,g,t,r) ->
          fprintf fmt "@[<hov 2>let@ %a%a %a = %a @]" prrec r string x gen g 
            term t
      | DGen g ->
          fprintf fmt "@[INTROS %a@]" gen g
    and theory fmt t = list newline decl fmt t in
    decl

  let theory ?kind fmt t =
    list newline (decl ?kind) fmt t
end
