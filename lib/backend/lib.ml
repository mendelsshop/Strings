let run program =
  let expr = Alpha_renaming.alpha_rename_tls program in
  (* let _functions, lexpr = Closure_conversion.closure_convert_tls expr in *)
  let mexpr = Monomorphization.monomorphize_tls expr in
  print_endline (Monomorphization.program_to_string mexpr)
