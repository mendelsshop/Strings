(* TODO: issues
   how to monomorphize letrecs - (polymorphic recursion issues?) - fix each let(rec) whether at the top level or not will have multiple copies of the `let pat = expr`
   something like:
   type 't let  { name: tpattern; value; 't mexpr; ty: ty; span: span }  maybe do not need span
   type 't mexpr
   | MLet { lets: 't let; e2: 't mexpr; span: span; ty: ty }
   | MLetRec { lets: 't let; e2: 't mexpr; span: span; ty: ty }
   ...
   type 't top_levl
   | MBind { lets: 't let; e2: 't mexpr;  }
   | MRecBind { lets: 't let;  }
   ...
*)
