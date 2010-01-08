open Ocamlbuild_plugin
open Command (*-- no longer needed for OCaml >= 3.10.2 *)

module P = Ocamlbuild_pack
open Ocamlbuild_plugin

let notags=Ocamlbuild_pack.Tags.of_list []

let ocamldep_command' tags spec =
  let tags' = tags++"ocaml"++"ocamldep" in
    S [!Options.ocamldep; T tags'; 
    P.Ocaml_utils.ocaml_ppflags (tags++"pp:dep");
       spec; A "-modules"]
let menhir_ocamldep_command' tags ~menhir_spec ~ocamldep_spec out =
  let menhir = if !Options.ocamlyacc = N then V"MENHIR" else !Options.ocamlyacc in
  Cmd(S[menhir; T tags; A"--raw-depend";
	A"--ocamldep"; Quote (ocamldep_command' notags ocamldep_spec);
	menhir_spec ; Sh ">"; Px out])

let menhir_ocamldep_command arg out env _build =
  let arg = env arg and out = env out in
  let tags = tags_of_pathname arg++"ocaml"++"menhir_ocamldep" in
  let ocamldep_spec = P.Tools.flags_of_pathname arg in
  menhir_ocamldep_command' tags ~menhir_spec:(P arg) ~ocamldep_spec out

let import_mlypack build mlypack =
  let tags1 = tags_of_pathname mlypack in
  let files = string_list_of_file mlypack in
  let include_dirs = Pathname.include_dirs_of (Pathname.dirname mlypack) in
  let files_alternatives =
    List.map begin fun module_name ->
      expand_module include_dirs module_name ["mly"]
    end files
  in
  let files = List.map Outcome.good (build files_alternatives) in
  let tags2 =
    List.fold_right
      (fun file -> Tags.union (tags_of_pathname file))
      files tags1
  in
  (Tags.remove "only_tokens" tags2, files)

let menhir_modular_ocamldep_command mlypack out env build =
  let mlypack = env mlypack and out = env out in
  let (tags,files) = import_mlypack build mlypack in
  let tags = tags++"ocaml"++"menhir_ocamldep" in
  let menhir_base = Pathname.remove_extensions mlypack in
  let menhir_spec = S[A "--base" ; P menhir_base ; 
    P.Command.atomize_paths files] in
  let ocamldep_spec = N in
  menhir_ocamldep_command' tags ~menhir_spec ~ocamldep_spec out

let menhir_modular menhir_base mlypack mlypack_depends env build =
  let menhir = if !Options.ocamlyacc = N then V"MENHIR" else !Options.ocamlyacc in
  let menhir_base = env menhir_base in
  let mlypack = env mlypack in
  let mlypack_depends = env mlypack_depends in
  let (tags,files) = import_mlypack build mlypack in
  let () = List.iter Outcome.ignore_good (build [[mlypack_depends]]) in
  P.Ocaml_compiler.prepare_compile build mlypack;
  let ocamlc_tags = tags++"ocaml"++"byte"++"compile" in
  let tags = tags++"ocaml"++"parser"++"menhir" in
  Cmd(S[menhir ;
        A "--ocamlc"; Quote(S[!Options.ocamlc; T ocamlc_tags; 
        P.Ocaml_utils.ocaml_include_flags mlypack]);
        T tags ; A "--infer" ; P.Tools.flags_of_pathname mlypack ;
        A "--base" ; Px menhir_base ; P.Command.atomize_paths files])


(* these functions are not really officially exported *)
let run_and_read = P.My_unix.run_and_read
let blank_sep_strings = P.Lexers.blank_sep_strings

let split s ch =
  let x = ref [] in
  let rec go s =
    let pos = String.index s ch in
    x := (String.before s pos)::!x;
    go (String.after s (pos + 1))
  in
  try
    go s
  with Not_found -> !x
                                                                                                                                                                                                                                             
let split_nl s = split s '\n'

let before_space s =
  try
    String.before s (String.index s ' ')
  with Not_found -> s

(* this lists all supported packages *)
let find_packages () =
  List.map before_space (split_nl & run_and_read "ocamlfind list")

(* this is supposed to list available syntaxes, but I don't know how to do it. *)
let find_syntaxes () = ["camlp4o"; "camlp4r"]

(* ocamlfind command *)
let ocamlfind x = S[A"ocamlfind"; x]

let _ = dispatch begin function
   | Before_options ->
       (* by using Before_options one let command line options have an higher priority *)
       (* on the contrary using After_options will guarantee to have the higher priority *)

       (* override default commands by ocamlfind ones *)
       Options.ocamlc     := ocamlfind & A"ocamlc";
       Options.ocamlopt   := ocamlfind & A"ocamlopt";
       Options.ocamldep   := ocamlfind & A"ocamldep";
       Options.ocamldoc   := ocamlfind & A"ocamldoc";
       Options.ocamlmktop := ocamlfind & A"ocamlmktop";
       
       (* custom modifications *)
       Options.use_menhir := true;
       Options.ocaml_cflags := "-dtypes" :: !Options.ocaml_cflags;
   | After_rules ->
       flag ["ocaml"; "parser"; "menhir"; "only_tokens" ] (A"--only-tokens");
       flag ["ocaml"; "menhir_ocamldep"; "only_tokens" ] (A"--only-tokens");
       flag ["ocaml"; "parser"; "menhir"; "use_tokens" ] (S [A"--external-tokens"; A "Tokens"]);
         
       rule "ocaml: menhir dependencies0"
         ~prod: "%.mly.depends"
         ~dep: "%.mly"
         ~insert: (`before "ocaml: menhir dependencies")
         (menhir_ocamldep_command "%.mly" "%.mly.depends");

       rule "ocaml: modular menhir (mlypack)0"
         ~prods:["%.mli" ; "%.ml"]
         ~deps:["%.mlypack"]
         ~insert:(`before "ocaml: modular menhir (mlypack)")
         (menhir_modular "%" "%.mlypack" "%.mlypack.depends");

       rule "ocaml: menhir modular dependencies0"
         ~prod:"%.mlypack.depends"
         ~dep:"%.mlypack"
         ~insert:(`before "ocaml: menhir modular dependencies")
         (menhir_modular_ocamldep_command "%.mlypack" "%.mlypack.depends");
       ocaml_lib ~extern:true "nums";
       (* When one link an OCaml library/binary/package, one should use -linkpkg *)
       flag ["ocaml"; "link"] & A"-linkpkg";

       (* For each ocamlfind package one inject the -package option when
        * compiling, computing dependencies, generating documentation and
        * linking. *)
       List.iter begin fun pkg ->
         flag ["ocaml"; "compile";  "pkg_"^pkg] & S[A"-package"; A pkg];
         flag ["ocaml"; "ocamldep"; "pkg_"^pkg] & S[A"-package"; A pkg];
         flag ["ocaml"; "doc";      "pkg_"^pkg] & S[A"-package"; A pkg];
         flag ["ocaml"; "link";     "pkg_"^pkg] & S[A"-package"; A pkg];
       end (find_packages ());

       (* Like -package but for extensions syntax. Morover -syntax is useless
        * when linking. *)
       List.iter begin fun syntax ->
         flag ["ocaml"; "compile";  "syntax_"^syntax] & S[A"-syntax"; A syntax];
         flag ["ocaml"; "ocamldep"; "syntax_"^syntax] & S[A"-syntax"; A syntax];
         flag ["ocaml"; "doc";      "syntax_"^syntax] & S[A"-syntax"; A syntax];
       end (find_syntaxes ());

       (* The default "thread" tag is not compatible with ocamlfind.
       Indeed, the default rules add the "threads.cma" or "threads.cmxa"
       options when using this tag. When using the "-linkpkg" option with
       ocamlfind, this module will then be added twice on the command line.

       To solve this, one approach is to add the "-thread" option when using
       the "threads" package using the previous plugin.
       *)
       flag ["ocaml"; "pkg_threads"; "compile"] (S[A "-thread"]);
       flag ["ocaml"; "pkg_threads"; "link"] (S[A "-thread"]);
       flag ["ocaml"; "compile"; "warn_error" ] (S[A "-w"; A "Z"; A "-warn-error"; A "A"]);
       (* Menhir --explain flag *)
       flag ["menhir"] (S[A"--explain"]);
       
   | _ -> ()
end

