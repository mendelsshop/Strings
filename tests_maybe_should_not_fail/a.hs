-- let x = \x. match x with 
-- | 1 -> 2
--  | bar -> 1
-- let x = \x. match x with 
-- | x -> 2
-- let z = if true then 1 else 4
let x = \a. match a with 
| M  z  -> {a = 2; b = 3}
| C  b  -> {a = 2; c = 4}
-- reason: we cannot say anything more than {a: int}, but some cases return more, since expression are "closed" they do not unify, maybe somehow return {a: int}
