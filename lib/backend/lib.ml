let run program =
  let expr = Alpha_renaming.alpha_rename_tls program in
  let expr = Simplify_calls.simplify_tls expr in
  print_endline (Typed_ast.program_to_string expr);
  let mexpr = Monomorphization.monomorphize_tls expr in
  let _functions, _lexpr = Closure_conversion.closure_convert_tls mexpr in
  print_endline (Monomorphization.program_to_string mexpr)
