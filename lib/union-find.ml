type 'a root = { mutable rank : int; mutable data : 'a }

type 'a parent_pointer_tree = [ `node of 'a elem | `root of 'a root ]
and 'a elem = { mutable parent : 'a parent_pointer_tree ref }

let make data = ref (`root { rank = 0; data })

let rec find_set (x : 'a parent_pointer_tree) =
  match x with `root _ as x -> x | `leaf { parent } -> find_set !parent
