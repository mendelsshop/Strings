open Utils
open Types
open Typed_ast
module IntegerSet = Set.Make (Int)
module FloatSet = Set.Make (Float)
module StringSet = Set.Make (String)

type space =
  | SInteger of IntegerSet.t
  | SString of StringSet.t
  | SFloat of FloatSet.t
  (* this doesn't have to be list its just two value *)
  | SBoolean of bool
  (* do we need unit as its only one value, meaning it could be just be a var *)
  | SUnit
  | SVar
  | SNominal of { value : space; name : string; id : int }
  | SRecord of space StringMap.t
  | SVariant of space StringMap.t

(* maybe this can be combined with combine space *)
let rec space_subset s1 s2 =
  match (s1, s2) with
  (* for constants like integers/strings/floats since this is only used for redudedant pattern checking so it suffices to make sure all possible value in s1 are in s2 *)
  | SInteger s1, SInteger s2 -> IntegerSet.diff s1 s2 |> IntegerSet.is_empty
  | SFloat s1, SFloat s2 -> FloatSet.diff s1 s2 |> FloatSet.is_empty
  | SString s1, SString s2 -> StringSet.diff s1 s2 |> StringSet.is_empty
  | SRecord s1, SRecord s2 ->
      StringMap.merge
        (fun _ s1 s2 ->
          Option.fold s1
            ~some:(fun s1' ->
              Option.fold s2
                ~some:(fun s2' -> space_subset s1' s2' |> Option.some)
                ~none:(Some false))
            ~none:(Some true))
        s1 s2
      |> StringMap.for_all (fun _ b -> b)
  | SVariant s1, SVariant s2 ->
      StringMap.merge
        (fun _ s1 s2 ->
          Option.fold s1
            ~some:(fun s1' ->
              Option.fold s2
                ~some:(fun s2' -> space_subset s1' s2' |> Option.some)
                ~none:(Some false))
            ~none:(Some true))
        s1 s2
      |> StringMap.for_all (fun _ b -> b)
  | SBoolean b1, SBoolean b2 -> b1 = b2
  | SUnit, SUnit -> true
  | ( SNominal { value; name; id },
      SNominal { value = value1; name = name1; id = id1 } )
    when id = id1 && name = name1 ->
      space_subset value value1
  | SVar, SVar | _, SVar -> true
  | SVar, _ -> false
  | _, _ -> failwith "mismatch"

(* returns the flattened out row and if its closed *)
let rec flattern_row (ty : ty) =
  let _, `root { Union_find.data = ty'; _ } = Union_find.find_set ty in
  match ty' with
  | TyVar _ -> (StringMap.empty, false)
  | TyNominal _ | TyRecord _ | TyVariant _ | TyInteger | TyString | TyFloat
  | TyGenVar _ | TyBoolean | TyArrow _ | TyUnit ->
      failwith "unreachable"
  | TyRowEmpty -> (StringMap.empty, true)
  | TyRowExtend { label; field; rest_row } ->
      let map, is_open = flattern_row rest_row in
      (StringMap.add label field map, is_open)

(* is this type a subset of this space? *)
let rec type_subset ty s =
  let _, `root { Union_find.data = ty_data; _ } = Union_find.find_set ty in
  match (ty_data, s) with
  | TyBoolean, SBoolean _
  | TyInteger, SInteger _
  | TyString, SString _
  | TyFloat, SFloat _ ->
      false
  | TyUnit, SUnit -> false
  (* for variants/record need function from row type to type StringMap.t *)
  (* only difference from space_subset is that for variants if its open (end in a tyvar) then it will never be susbset *)
  | TyRecord s1, SRecord s2 ->
      let s1, _ = flattern_row s1 in
      StringMap.merge
        (fun _ s1 s2 ->
          Option.fold s1
            ~some:(fun s1' ->
              Option.fold s2
                ~some:(fun s2' -> type_subset s1' s2' |> Option.some)
                ~none:(Some false))
            ~none:(Some true))
        s1 s2
      |> StringMap.for_all (fun _ b -> b)
  | TyVariant s1, SVariant s2 ->
      let s1, closed = flattern_row s1 in
      closed
      && StringMap.merge
           (fun _ s1 s2 ->
             Option.fold s1
               ~some:(fun s1' ->
                 Option.fold s2
                   ~some:(fun s2' -> type_subset s1' s2' |> Option.some)
                   ~none:(Some false))
               ~none:(Some true))
           s1 s2
         |> StringMap.for_all (fun _ b -> b)
  | _, SVar -> true
  | ( TyNominal { id; name; ty : _ },
      SNominal { id = id'; name = name'; value : _ } )
    when id = id' && name = name' ->
      type_subset ty value
  | _ -> failwith "mismatch"

let rec combine_space s1 s2 =
  match (s1, s2) with
  | SInteger s1, SInteger s2 -> SInteger (IntegerSet.union s1 s2)
  | SRecord s1, SRecord s2 ->
      SRecord
        (StringMap.merge
           (fun _ s1 s2 ->
             Option.fold s1
               ~some:(fun s1' ->
                 Option.fold s2
                   ~some:(fun s2' -> combine_space s1' s2' |> Option.some)
                   ~none:s1)
               ~none:s2)
           s1 s2)
  | SVariant s1, SVariant s2 ->
      SVariant
        (StringMap.merge
           (fun _ s1 s2 ->
             Option.fold s1
               ~some:(fun s1' ->
                 Option.fold s2
                   ~some:(fun s2' -> combine_space s1' s2' |> Option.some)
                   ~none:s1)
               ~none:s2)
           s1 s2)
  | SString s1, SString s2 -> SString (StringSet.union s1 s2)
  | SFloat s1, SFloat s2 -> SFloat (FloatSet.union s1 s2)
  | SBoolean b1, SBoolean b2 -> if b1 = b2 then SBoolean b1 else SVar
  | SUnit, SUnit -> SUnit
  | ( SNominal { value; name; id },
      SNominal { value = value1; name = name1; id = id1 } )
    when id = id1 && name = name1 ->
      SNominal { name = name1; id; value = combine_space value value1 }
  | SVar, _ | _, SVar -> SVar
  | _, _ -> failwith "mismatch"

let rec pattern_to_space = function
  | PTVar _ -> SVar
  | PTWildcard _ -> SVar
  | PTInteger { value; _ } -> SInteger (IntegerSet.singleton value)
  | PTFloat { value; _ } -> SFloat (FloatSet.singleton value)
  | PTString { value; _ } -> SString (StringSet.singleton value)
  | PTBoolean { value; _ } -> SBoolean value
  | PTRecord { fields; _ } ->
      SRecord
        (fields
        |> List.map (fun { Ast.label; value } ->
               (label, pattern_to_space value))
        |> StringMap.of_list)
  | PTConstructor { name; value; _ } ->
      SVariant (StringMap.singleton name (pattern_to_space value))
  | PTNominalConstructor { name; id; value; _ } ->
      SNominal { name; id; value = pattern_to_space value }
  | PTUnit _ -> SUnit
  | PTOr { patterns = pattern :: patterns; _ } ->
      let pattern = pattern_to_space pattern in
      let patterns = List.map pattern_to_space patterns in

      (* TODO: check for redudant inner patterns *)
      List.fold_left combine_space pattern patterns
  | PTOr _ -> failwith "unreachable"
  | PTAs { value; _ } -> pattern_to_space value

(* exhaustiveness checking: combine all the patterns into one big space and then see if the type is a subset of this *)
(* rededundent checking: as we combine the patterns check if the current space is a subset of the accumulated space *)
(* these two can be done together *)
