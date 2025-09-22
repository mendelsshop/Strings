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

(* no infiinte reucstion becasue althouth types can be infinite, since: *)
(* 1: within a row there should not be infinity so flattening should not cause infinite recursion *)
(* 2: bdcause the space itself is not infinite we only go as far as the space "unwraps" *)

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

(* used for exhaustiveness checking *)
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

(* patterns that are redudundent *)
let duplicate_patterns : ty tpattern list ref = ref []
let mcons e l = l := e :: !l

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

      (* TODO: check for redudant inner patterns *)
      List.fold_left combine_space pattern patterns
  | PTOr _ -> failwith "unreachable"
  | PTAs { value; _ } -> pattern_to_space value

(* combine accumulated space with new space *)
(* also accumulate a lit of redudedant patterns from the new space when compared to accumulated space *)
and combine_space s p =
  match (s, p) with
  | SInteger s, PTInteger { value; _ } ->
      if IntegerSet.mem value s then mcons p duplicate_patterns;
      SInteger (IntegerSet.add value s)
  | SFloat s, PTFloat { value; _ } ->
      if FloatSet.mem value s then mcons p duplicate_patterns;
      SFloat (FloatSet.add value s)
  | SString s, PTString { value; _ } ->
      if StringSet.mem value s then mcons p duplicate_patterns;
      SString (StringSet.add value s)
  | SBoolean b1, PTBoolean { value; _ } ->
      if b1 = value then (
        mcons p duplicate_patterns;
        SBoolean b1)
      else SVar
  | SUnit, PTUnit _ ->
      mcons p duplicate_patterns;
      SUnit
  | ( SNominal { value; name; id },
      PTNominalConstructor { value = value1; name = name1; id = id1; _ } )
    when id = id1 && name = name1 ->
      let value = combine_space value value1 in
      SNominal { name = name1; id; value }
  | SVar, (PTVar _ | PTWildcard _) ->
      mcons p duplicate_patterns;
      SVar
  | _, (PTVar _ | PTWildcard _) -> SVar
  | _, PTAs { value; _ } -> combine_space s value
  | SRecord s1, PTRecord { fields; _ } ->
      let s2 =
        fields
        |> List.map (fun { Ast.label; value } -> (label, value))
        |> StringMap.of_list
      in
      let fields =
        StringMap.merge
          (fun _ s1 s2 ->
            Option.fold s1
              ~some:(fun s1' ->
                Option.fold s2
                  ~some:(fun s2' -> combine_space s1' s2' |> Option.some)
                  ~none:(Some s1'))
              ~none:(Option.map (fun s2' -> pattern_to_space s2') s2))
          s1 s2
      in
      SRecord fields
  | SVariant s1, PTConstructor { name; value; _ } ->
      let s1 =
        StringMap.update name
          (fun s1 ->
            Option.fold s1
              ~some:(fun s1 ->
                let s1 = combine_space s1 value in
                s1)
              ~none:(pattern_to_space value)
            |> Option.some)
          s1
      in
      SRecord s1
  | _, PTOr { patterns; _ } ->
      (* TODO: check for redudant inner patterns *)
      List.fold_left combine_space s patterns
  | _, _ -> failwith "mismatch"

(* exhaustiveness checking: combine all the patterns into one big space and then see if the type is a subset of this *)
(* rededundent checking: as we combine the patterns check if the current space is a subset of the accumulated space *)
(* these two can be done together *)
