open Myformat

let output s = 
  let c = open_out !Options.outfile in
  let fmt = formatter_of_out_channel c in
  Sectionize.print_all fmt s;
  pp_print_flush fmt ();
  close_out c
