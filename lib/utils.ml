(* open Monad *)
(* open Monad.ResultReaderOps *)
include Gensym
open AMPCL
module Subst = Map.Make (String)
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

(* TODO: highlight the whole span *)
let reach_offset ({ start; finish = _ } : span) i =
  let n = start in
  let len = String.length i in
  let line_number =
    let rec inner line start =
      try
        let newline = String.index_from i start '\n' in
        if newline >= n then line else inner (line + 1) (start + newline + 1)
      with Not_found | Invalid_argument _ -> line
    in
    inner 1 0
  in

  let start =
    try
      String.rindex_from_opt i (n - 1) '\n'
      |> Option.fold ~some:(( + ) 1) ~none:0
    with Invalid_argument _ -> 0
  in
  let end_index =
    String.index_from_opt i n '\n' |> Option.fold ~some:Fun.id ~none:len
  in
  let colum_index = n - start in
  let substr = String.sub i start (end_index - start) in
  let substr = substr |> explode in
  let substr = substr |> List.mapi (fun a b -> (a, b)) in
  let colum_index, substr =
    substr
    |> List.fold_left
         (fun (c : int * char list) (i : int * char) ->
           ( (if fst i >= colum_index then fst c
              else if snd i = '\t' then fst c + 4
              else fst c + 1),
             if snd i = '\t' then snd c @ (' ' :: ' ' :: ' ' :: ' ' :: [ ' ' ])
             else snd c @ [ snd i ] ))
         (0, [])
  in
  let substr = substr |> implode in
  ( { line = line_number; column = colum_index + 1 },
    Some (if substr = "" then "<empty line>" else substr) )

let combine_spans : span -> span -> span =
 fun { start; finish } { start = start'; finish = finish' } ->
  { start = min start start'; finish = max finish finish' }

let span_to_line_highlight : span -> string -> string =
 fun span file ->
  let pos = reach_offset span file in
  string_of_int (fst pos).line
  ^ ":"
  ^ string_of_int (fst pos).column
  ^ ":\n"
  ^ Option.fold
      ~some:(fun s ->
        "  |\n"
        ^ string_of_int (fst pos).line
        ^ " | " ^ s ^ "\n  |"
        ^ String.make (fst pos).column ' '
        ^ "^\n")
      ~none:"" (snd pos)

module type T = sig
  type t
end

module Env = struct
  module type S = sig
    include Map.S

    val union : 'a t -> 'a t -> 'a t
  end

  module Make (T : T) = struct
    include StringMap

    type t = T.t StringMap.t

    let union x y = union (fun _ x _ -> Some x) x y
  end
end
(* let in_env new_env m = *)
(*   let scope env = new_env @ env in *)
(*   R.local scope m *)
(**)
(* let new_meta = *)
(*   let* letters = ST.get () |> R.lift |> lift in *)
(*   let* letter, letters' = *)
(*     Stdlib.Option.fold *)
(*       ~none:(fail "Ran out of fresh type variables.") *)
(*       ~some:(fun (letter, letters') -> (letter, letters') |> return) *)
(*       (Stdlib.Seq.uncons letters) *)
(*   in *)
(*   let* _ = ST.put letters' |> R.lift |> lift in *)
(*   return letter *)
(* let run e env = (run e |> R.run) env |> ST.run *)
(* let run_with_default e : ('a, string) result = run e [] letters |> fst *)
