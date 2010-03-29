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
and gen = string list * string list * string list
and funcbody = t * t * t
and isrec = ty Const.isrec

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
          effect eff (maycap string) cap print t2
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


end
