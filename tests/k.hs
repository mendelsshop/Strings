-- let x = \x. match x with 
-- | 1 -> 2
--  | bar -> 1
-- let x = \x. match x with 
-- | x -> 2
-- let z = if true then 1 else 4
let x = \a. match a with 
| M  z  -> 2
| C  b  -> 2
