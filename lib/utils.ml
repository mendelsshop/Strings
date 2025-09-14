(* open Monad *)
(* open Monad.ResultReaderOps *)
include Gensym
module Subst = Map.Make (String)
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

module type T = sig
  type t
end

module Env (T : T) = struct
  include StringMap

  type t = T.t StringMap.t

  let union x y = union (fun _ x _ -> Some x) x y
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
