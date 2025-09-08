open Monads.Std
open Types

let ( << ) f g x = f (g x)

module ST = struct
  module StateEnv = struct
    type t = string Seq.t
  end

  include Monad.State.T1 (StateEnv) (Monad.Ident)
  include Monad.State.Make (StateEnv) (Monad.Ident)
end

module R = struct
  module ReaderEnv = struct
    type t = (string * ty) list
  end

  module Reader = Monad.Reader.T1 (ReaderEnv) (ST)
  include Reader
  include Monad.Reader.Make (ReaderEnv) (ST)

  let _ = run

  let local f r =
    let f' e = run r (f e) |> lift in
    bind ~f:f' (read ())
end

module Err = struct
  type t = string
end

module ResultReader = Monad.Result.T1 (Err) (R)
module ResultReaderOps = Monad.Result.Make (Err) (R)
open ResultReaderOps

let get x =
  let* env = lift (R.read ()) in
  Option.fold
    ~some:(fun x -> return x)
    ~none:("Unbound variable " ^ x ^ "." |> ResultReaderOps.fail)
    (env
    |> Stdlib.List.find_map (fun ((name : string), ty) ->
           if name = x then Some ty else None))

let chars = Stdlib.Seq.init 26 (fun x -> 97 + x |> Char.chr |> String.make 1)

let rec replicate n seq =
  let open Stdlib in
  if n = 0 then Seq.return ""
  else
    Seq.flat_map
      (fun res ->
        Seq.flat_map
          (fun rest -> res ^ rest |> Seq.return)
          (replicate (n - 1) seq))
      seq

let letters =
  let open Stdlib in
  Seq.ints 1 |> Seq.flat_map (fun x -> replicate x chars)
