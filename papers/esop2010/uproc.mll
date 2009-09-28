{
  let buf = Buffer.create 1024
}

let blank = [ ' ' '\n' '\t' ]
let notblank = [ ^ ' ' '\n' '\t' '#' '0' - '9' ]+

rule scan = parse
    | blank (notblank as id) (['0' - '9'] as x) blank
      { Buffer.add_string buf (Format.sprintf " %s_%c " id x) ; scan lexbuf }
    | "/\\" { Buffer.add_string buf "~\\wedge~" ; scan lexbuf }
    | "\\/" { Buffer.add_string buf "~\\vee~" ; scan lexbuf }
    | "==" { Buffer.add_string buf "\\equiv " ; scan lexbuf }
    | "<->" { Buffer.add_string buf "\\leftrightarrow " ; scan lexbuf }
    | "->"   { Buffer.add_string buf "\\rightarrow " ; scan lexbuf}
    | "-->"  { Buffer.add_string buf "\\longrightarrow " ; scan lexbuf}
    | "--\\" { Buffer.add_string buf "\\rightharpoonup " ; scan lexbuf}
    | "|->"  { Buffer.add_string buf "\\mapsto " ; scan lexbuf}
    | "=>"   { Buffer.add_string buf "\\Rightarrow " ; scan lexbuf}
    | "<=>"  { Buffer.add_string buf "\\Leftrightarrow " ; scan lexbuf}
    | "->>"  { Buffer.add_string buf "\\twoheadrightarrow " ; scan lexbuf}
    | "[|"   { Buffer.add_string buf "\\llbracket " ; scan lexbuf}
    | "|]"   { Buffer.add_string buf "\\rrbracket " ; scan lexbuf}
    | "|="   { Buffer.add_string buf "\\models " ; scan lexbuf}
    | "||="  { Buffer.add_string buf "\\Vdash " ; scan lexbuf}
    | "|-"   { Buffer.add_string buf "\\vdash " ; scan lexbuf}
    | eof { () }
    | _ as c { Buffer.add_char buf c; scan lexbuf }

{
let _ = 
  let c = Lexing.from_channel stdin in
  scan c;
  Buffer.output_buffer stdout buf
}
