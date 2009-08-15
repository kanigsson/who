include Format

type 'a fmt = Format.formatter -> 'a -> unit

let rec print_list sep prf fmt = function
  | [] -> ()
  | [x] -> prf fmt x
  | (x::xs) -> prf fmt x; sep fmt (); print_list sep prf fmt xs

let comma fmt () = pp_print_string fmt ","
let semi fmt () = pp_print_string fmt ";"
let space fmt () = fprintf fmt "@ "
let nothing _ () = ()
let double_newline fmt () = fprintf fmt "@\n@\n"
let newline fmt () = fprintf fmt "@\n"
let lbrack fmt () = pp_print_string fmt "["
let rbrack fmt () = pp_print_string fmt "]"

let optlist pr fmt = function
  | [] -> space fmt ()
  | l -> fprintf fmt "@ [%a]@ " (print_list space pr) l

let opt_print prf fmt = function
  | None -> ()
  | Some x -> prf fmt x

let pr_opt_string fmt s = opt_print pp_print_string fmt s

let sprintf s =
  ignore(flush_str_formatter ());
  kfprintf (fun _ -> flush_str_formatter ()) str_formatter s

let print_set fmt s = 
  Misc.SS.iter (fun x -> pp_print_string fmt x ; space fmt ()) s


let hash_print ?(bsep=lbrack) ?(endsep=rbrack) prk prv fmt h =
  bsep fmt ();
  Hashtbl.iter (fun k v -> fprintf fmt "%a|->%a;" prk k prv v) h;
  endsep fmt ()
