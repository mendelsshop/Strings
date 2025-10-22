open Utils

module Parsed = struct
  type ty =
    | TyCon of { name : string; arguements : ty list }
    | TyUnit
    | TyInteger
    | TyString
    | TyFloat
    | TyBoolean
    | TyArrow of { domain : ty; range : ty }
    | TyRecord of { fields : ty row; extends_record : ty Option.t }
    | TyVariant of { variants : ty row }

  let rec type_to_string = function
    | TyCon { name; arguements } ->
        (if List.is_empty arguements then ""
         else
           "("
           ^ (List.map type_to_string arguements |> String.concat ", ")
           ^ ") ")
        ^ name
    | TyUnit -> "()"
    | TyInteger -> "integer"
    | TyString -> "string"
    | TyFloat -> "float"
    | TyBoolean -> "boolean"
    | TyRecord _ -> failwith ""
    | TyVariant _ -> failwith ""
    | TyArrow { domain; range } ->
        let x_string = type_to_string domain in
        let y_string = type_to_string range in
        x_string ^ " -> " ^ y_string
end

type 't ty_f =
  | TyVar of { name : string; level : int }
  | TyUnit
  | TyInteger
  | TyString
  | TyFloat
  | TyBoolean
  | TyArrow of { domain : 't; range : 't }
  | TyRowEmpty
  | TyRowExtend of { label : string; field : 't; rest_row : 't }
  | TyRecord of 't
  | TyVariant of 't
  | TyGenVar of string
  | TyNominal of { name : string; id : int; ty : 't }

type 't type_decl = {
  name : string;
  kind : 't type_decl_kind;
  ty_variables : StringSet.t;
  span : AMPCL.span;
}

and 't type_decl_kind =
  | TypeDecl of 't
  | NominalTypeDecl of { ty : 't; id : int }

type ty = 'a ty_f Union_find.elem as 'a

let ftv_ty (ty : ty) =
  let rec inner ty used =
    let root, `root node = Union_find.find_set ty in
    if List.memq root used then StringSet.empty
    else
      match node.data with
      | TyVar { name; _ } -> StringSet.singleton name
      | TyGenVar _ -> StringSet.empty (* maybe free? *)
      | TyArrow { domain; range } ->
          StringSet.union
            (inner domain (root :: used))
            (inner range (root :: used))
      | TyRecord r -> inner r (root :: used)
      | TyVariant v -> inner v (root :: used)
      | TyNominal { ty; _ } -> inner ty (root :: used)
      | TyRowExtend { field; rest_row; _ } ->
          StringSet.union
            (inner field (root :: used))
            (inner rest_row (root :: used))
      | TyString | TyBoolean | TyRowEmpty | TyUnit | TyInteger | TyFloat ->
          StringSet.empty
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
             | TyVar { name; _ } -> (name, [])
             | TyNominal { name; ty; id; _ } ->
                 let ty, used' = inner ((root, sym) :: used) ty in
                 (name ^ string_of_int id ^ "(" ^ ty ^ ")", used')
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
             | TyRowExtend { label; field; rest_row } ->
                 let field, used' = inner ((root, sym) :: used) field in
                 let row_extension, used'' =
                   inner ((root, sym) :: used) rest_row
                 in
                 ( label ^ type_delim ^ field ^ delim ^ row_extension,
                   used' @ used'' )
             | TyVariant row ->
                 let t, used' =
                   inner ((root, sym) :: used) ~unit:"" ~delim:"| "
                     ~type_delim:" " row
                 in
                 ("(" ^ t ^ ")", used')
             | TyArrow { domain; range } ->
                 let x_string, used' = inner ((root, sym) :: used) domain in
                 let y_string, used'' = inner ((root, sym) :: used) range in
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
