
let out s = 
  let f = !Options.outfile in
  Cmd.print_to_file `Pangoline f s
  
  
