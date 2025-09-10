open Utils

type 't ty_f =
  | TyVar of string * int
  | TyUnit
  | TyInteger
  | TyString
  | TyFloat
  | TyBoolean
  | TyArrow of 't * 't
  | TyRowEmpty
  | TyRowExtend of string * 't * 't
  | TyRecord of 't
  | TyVariant of 't
  | TyGenVar of string

type ty = 'a ty_f Union_find.elem as 'a

let ftv_ty (ty : ty) =
  let rec inner ty used =
    let root, `root node = Union_find.find_set ty in
    if List.memq root used then StringSet.empty
    else
      match node.data with
      | TyVar (v, _) -> StringSet.singleton v
      | TyGenVar _ -> StringSet.empty (* maybe free? *)
      | TyArrow (p, r) ->
          StringSet.union (inner p (root :: used)) (inner r (root :: used))
      | TyRecord r -> inner r (root :: used)
      | TyVariant v -> inner v (root :: used)
      | TyRowExtend (_, p, r) ->
          StringSet.union (inner p (root :: used)) (inner r (root :: used))
      | TyString | TyBoolean | TyRowEmpty | TyUnit | TyInteger | TyFloat -> StringSet.empty
  in
  inner ty []

let type_to_string ty =
  let rec inner used ?(type_delim = ": ") ?(delim = "; ") ?(unit = "{}") ty =
    let root, `root node = Union_find.find_set ty in
    (List.assq_opt root used
    |> Option.fold
         ~some:(fun t () -> (t, [ ty ]))
         ~none:(fun () ->
           let sym = gensym () in
           let string, used =
             match node.data with
             | TyVar (v, _) -> (v, [])
             | TyGenVar v -> (v, [])
             | TyUnit -> ("()", [])
             | TyInteger -> ("integer", [])
             | TyString -> ("string", [])
             | TyFloat -> ("float", [])
             | TyBoolean -> ("boolean", [])
             | TyRowEmpty -> (unit, [])
             | TyRecord t ->
                 let t, used' = inner ((root, sym) :: used) ~unit:"" t in
                 ("{ " ^ t ^ " }", used')
             | TyRowExtend (label, field, row_extension) ->
                 let field, used' = inner ((root, sym) :: used) field in
                 let row_extension, used'' =
                   inner ((root, sym) :: used) row_extension
                 in
                 ( label ^ type_delim ^ field ^ delim ^ row_extension,
                   used' @ used'' )
             | TyVariant row ->
                 let t, used' =
                   inner ((root, sym) :: used) ~unit:"" ~delim:"| "
                     ~type_delim:" " row
                 in
                 ("(" ^ t ^ ")", used')
             | TyArrow (x, y) ->
                 let x_string, used' = inner ((root, sym) :: used) x in
                 let y_string, used'' = inner ((root, sym) :: used) y in
                 let used' = used' @ used'' in
                 (x_string ^ " -> " ^ y_string, used')
           in
           let recursive_prefix =
             if List.memq root used then "recursive " ^ sym ^ ". " else ""
           in
           (recursive_prefix ^ string, used)))
      ()
  in

  inner [] ty |> fst
