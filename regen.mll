{
open Format

module type Output = sig
  type t

  val fmt : formatter
  val print : formatter -> t -> unit
  val id : t -> string
  val force_newline : t -> bool
end

module Make (O : Output) = struct

  let print_elt fmt x =
    if O.force_newline x then
      fprintf fmt "@\n(*who%s*)@\n%a (*who*)@\n" (O.id x) O.print x
    else
      fprintf fmt "(*who%s*) %a (*who*) @," (O.id x) O.print x

  let print_until fmt ?identifier acc = 
    match identifier with
    | None -> List.iter (print_elt fmt) acc; []
    | Some id ->
        let rec aux = function
          | [] -> 
              printf "finished@.";
              []
          | x::xs ->
              let id' = O.id x in
              printf "comparing: %s and %s@." id id';
              if id' = id then begin (print_elt fmt) x; xs end
              else begin print_elt fmt x; aux xs end in
        aux acc

}

let alpha = ['a' - 'z' 'A'-'Z']
let digit = ['0'-'9']
let identifier = alpha (alpha | digit | '\'' | '_')*

rule skip acc = parse
  | "(*who*)" { () }
  | _ { skip acc lexbuf }
  | eof { 
    ignore (print_until O.fmt acc) }

and search_next acc = parse
  | "(*who" (identifier as identifier) "*)"
  { 
    printf "found %s@." identifier;
(*     fprintf O.fmt "%s@." s; *)
    let acc = print_until O.fmt ~identifier acc in
    skip acc lexbuf;
    search_next acc lexbuf
  }
  | _ as c { pp_print_char O.fmt c; search_next acc lexbuf }
  | eof { 
    ignore (print_until O.fmt acc) }

{
end

let main s = 
  let f = !Options.outfile in
  let in_buf, close_in = 
    match f with
    | "" -> Lexing.from_string "", (fun () -> () )
    | s when Sys.file_exists s ->
        let infile = s ^ ".bak" in
        let _ = Sys.command (sprintf "cp %s %s" s infile) in
        let cin = open_in infile in
        Lexing.from_channel cin, (fun () -> close_in cin)
    |  _ -> Lexing.from_string "", (fun () -> ()) in
  let ochan = open_out f in
  let module O = struct
    include Sectionize.Flatten
    let fmt = formatter_of_out_channel ochan
  end in
  let module Out = Make (O) in
  Out.search_next s in_buf;
  pp_print_flush O.fmt ();
  close_in ()

}
