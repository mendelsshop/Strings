let counter = ref 0

let gensym_int () =
  let counter' = !counter in
  incr counter;
  counter'

let gensym () = gensym_int () |> string_of_int
