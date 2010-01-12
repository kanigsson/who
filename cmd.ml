open Myformat

let do_ s = 
  printf "%s@." s;
  ignore (Sys.command s)
let chmod f = do_ (sprintf "chmod a-w %s" f)  
let cp f1 f2 = do_ (sprintf "cp %s %s" f1 f2)
let rm f = do_ (sprintf "rm -f %s" f)  

let pangoline f = do_ (sprintf "pangoline %s" f)

let print_to_file kind f s = 
  let c = open_out f in
  let fmt = formatter_of_out_channel c in
  Sectionize.print_all kind fmt s;
  close_out c

let diff3 myfile oldfile yourfile output =
  do_ (sprintf "diff3 -m %s %s %s > %s" myfile oldfile yourfile output)

let kdiff3 myfile oldfile yourfile output =
  do_ (sprintf "kdiff3 --auto %s %s %s -o %s" oldfile myfile yourfile output)

