(* open Types *)
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

let space_subset _s1 _s2 = failwith ""
let type_subset _ty _s = failwith ""

let rec combine_space s1 s2 =
  match (s1, s2) with
  | SInteger s1, SInteger s2 -> SInteger (IntegerSet.union s1 s2)
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
  | PTRecord _ -> SVar (* replace svar with actual handling of records *)
  | PTConstructor _ -> SVar (* replace svar with actual handling of variants *)
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
