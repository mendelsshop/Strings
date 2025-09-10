let counter = ref 0

let gensym () =
  let counter' = !counter in
  incr counter;
  string_of_int counter'
