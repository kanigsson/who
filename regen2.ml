open Myformat

let print_all fmt s =
  print_list newline Sectionize.Flatten.print fmt s

let cmd s = 
  printf "%s@." s;
  ignore (Sys.command s)
let chmod f = cmd (sprintf "chmod a-w %s" f)  
let cp f1 f2 = cmd (sprintf "cp %s %s" f1 f2)

let print_to_file f s = 
  let c = open_out f in
  let fmt = formatter_of_out_channel c in
  print_all fmt s;
  close_out c

let diff3 myfile oldfile yourfile output =
  cmd (sprintf "diff3 -m %s %s %s > %s" myfile oldfile yourfile output)

let main s = 
  let f = !Options.outfile in
  let orig = f ^ ".orig" in
  if Sys.file_exists orig && Sys.file_exists f then begin
    (* recreation mode *)
    let orig_old = orig ^ ".old" in
    let bak = f ^ ".bak" in
    cp orig orig_old;
    cp f bak;
    print_to_file orig s;
    diff3 bak orig_old orig f
  end else begin 
    assert (not (Sys.file_exists f));
    (* creation mode *)
    print_to_file orig s;
    cp orig f;
    chmod orig
  end

