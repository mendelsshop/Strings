type ty = Function of (ty * ty) | TypeIdent of string | WildCard
type 'a typed_opt = { ty : ty option; value : 'a }

type ast =
  | Float of float
  | Int of int
  | String of string
  | Ident of string
  | Application of (ast * ast list)

type fn = { args : string typed_opt list; abstraction : ast typed_opt }
