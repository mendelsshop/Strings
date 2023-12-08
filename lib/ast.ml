type ty = Function of (ty * ty) | Type of string | WildCard
type 'a typed_opt = { ty : ty option; value : 'a }
type ident = string

type ast =
  | Float of float
  | Int of int
  | String of string
  | Ident of ident
  | Application of { func : ast; arguements : ast list }
  | Function of { parameters : ident typed_opt list; abstraction : ast }
  | If of { condition : ast; consequent : ast; alternative : ast }
  | Let of { name : ident; value : ast }
