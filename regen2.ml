let main s = 
  let f = !Options.outfile in
  let orig = f ^ ".orig" in
  if Sys.file_exists orig && Sys.file_exists f then begin
    (* recreation mode *)
    let orig_old = orig ^ ".old" in
    let bak = f ^ ".bak" in
    Cmd.cp orig orig_old;
    Cmd.cp f bak;
    Cmd.print_to_file `Coq orig s;
    Cmd.diff3 bak orig_old orig f
  end else begin 
    assert (not (Sys.file_exists f));
    (* creation mode *)
    Cmd.print_to_file `Coq orig s;
    Cmd.cp orig f;
    Cmd.chmod orig
  end

