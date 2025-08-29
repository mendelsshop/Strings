type 'a root = { mutable rank : int; mutable data : 'a }

type 'a parent_pointer_tree = [ `node of 'a node | `root of 'a root ]
and 'a node = { mutable parent : 'a parent_pointer_tree ref }

type 'a elem = 'a parent_pointer_tree ref

let make data : 'a elem = ref (`root { rank = 0; data })

(* we return the root node as a reference and as dereferenced to use fancy polymorphic variants matching as root is always a root *)
let rec find_set (x : 'a elem) : 'a elem * [< `root of 'a root ] =
  match !x with
  | `root _ as x' -> (x, x')
  | `node link ->
      let res_ref, res = find_set link.parent in
      link.parent <- res_ref;
      (res_ref, res)

let union x y =
  let x_ref, `root x = find_set x in
  let y_ref, `root y = find_set y in
  if x_ref == y_ref then x_ref
  else if x.rank > y.rank then (
    y_ref := `node { parent = x_ref };
    x_ref)
  else if x.rank < y.rank then (
    x_ref := `node { parent = y_ref };
    y_ref)
  else (
    x_ref := `node { parent = y_ref };
    y.rank <- y.rank + 1;
    y_ref)
