module SM = Misc.StringMap

module Identifier = struct
  let equal_id = "="
  let empty_id = "empty"
  let not_id = "~"
  let leb_id = "<<="
  let ltb_id = "<<"
  let gtb_id = ">>"
  let geb_id = ">>="
  let eqb_id = "=="
  let neqb_id = "!="
  let andb_id = "band"
  let orb_id = "bor"
  let le_id = "<="
  let lt_id = "<"
  let ge_id = ">="
  let gt_id = ">"
  let neq_id = "<>"
  let and_id = "/\\"
  let or_id = "\\/"
  let impl_id = "->"

  let tuple_id = ","
  let fst_id = "fst"
  let snd_id = "snd"

  let plus_id = "+"
  let minus_id = "-"

  let combine_id = "combine"
  let restrict_id = "restrict"
  let get_id = "!!"
  let store_id = ":="


  let bool_id = "bool"
  let btrue_id = "true"
  let bfalse_id = "false"

  let unit_id = "unit"
  let void_id = "tt"

end

module Logic = struct
  open Identifier
  let equal_var = Name.from_string equal_id
  let empty_var = Name.from_string empty_id
  let not_var = Name.from_string not_id
  let leb_var = Name.from_string leb_id
  let ltb_var = Name.from_string ltb_id
  let gtb_var = Name.from_string gtb_id
  let geb_var = Name.from_string geb_id
  let eqb_var = Name.from_string eqb_id
  let neqb_var = Name.from_string neqb_id
  let andb_var = Name.from_string andb_id
  let orb_var = Name.from_string orb_id
  let le_var = Name.from_string le_id
  let lt_var = Name.from_string lt_id
  let ge_var = Name.from_string ge_id
  let gt_var = Name.from_string gt_id
  let neq_var = Name.from_string neq_id
  let and_var = Name.from_string and_id
  let or_var = Name.from_string or_id
  let impl_var = Name.from_string impl_id
  let tuple_var = Name.from_string tuple_id
  let fst_var = Name.from_string fst_id
  let snd_var = Name.from_string snd_id

  let plus_var = Name.from_string plus_id
  let minus_var = Name.from_string minus_id

  let combine_var = Name.from_string combine_id
  let restrict_var = Name.from_string restrict_id
  let get_var = Name.from_string get_id
  let store_var = Name.from_string store_id

  let btrue_var = Name.from_string btrue_id
  let bfalse_var = Name.from_string bfalse_id

  let void_var = Name.from_string void_id

  let allvars = [ equal_var ; empty_var ; not_var ; equal_var
      ; empty_var ; not_var ; leb_var ; ltb_var ; gtb_var 
      ; geb_var ; eqb_var ; neqb_var ; andb_var ; orb_var 
      ; le_var  ; lt_var  ; ge_var  ; gt_var  ; neq_var 
      ; and_var ; or_var ; impl_var ; tuple_var ; fst_var ; snd_var ;
      plus_var ; minus_var ; combine_var ; restrict_var ; get_var;
      store_var ; btrue_var ; bfalse_var ; void_var
  ]

  let map =
    List.fold_left (fun acc x ->
      SM.add (Name.unsafe_to_string x) x acc) SM.empty allvars

  let infix_set = 
    let infix_vars = 
      [equal_var ; leb_var ; ltb_var ; gtb_var ; geb_var ; eqb_var
      ; neqb_var ; andb_var ; orb_var ; le_var ; lt_var ; ge_var 
      ; gt_var ; neq_var ; and_var ; or_var ; impl_var ; tuple_var
      ; plus_var ; minus_var ; store_var ] in
    List.fold_right Name.S.add infix_vars Name.S.empty

  let effrec_set = 
    let effrec_vars = [ combine_var ; restrict_var ; empty_var ; get_var ] in
    List.fold_right Name.S.add effrec_vars Name.S.empty

  let pangoline_map = 
    let l = 
      [ 
        impl_var, "=>" ; 
        not_var, "not" ; 
        and_var, "and" ; 
        or_var, "or" ; 
      ] in
    List.fold_left (fun acc (a,b) -> Name.M.add a b acc) Name.M.empty l

end

module Ty = struct

  open Identifier

  let bool_var = Name.from_string bool_id
  let unit_var = Name.from_string unit_id

  let allvars = [ bool_var ; unit_var ]
  let map =
    List.fold_left (fun acc x ->
      SM.add (Name.unsafe_to_string x) x acc) SM.empty allvars
end
