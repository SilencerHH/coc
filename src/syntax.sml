structure Syntax = struct

  type loc = Report.loc

  datatype exp' =
    Prop
    | Var of string
    | Pi of string * exp * exp
    | Lam of string * exp option * exp
    | App of exp * exp
    | Let of string * exp option * exp * exp
    | Hole
  withtype exp = loc * exp'

  datatype cmd' = Axiom of string * exp | Def of string * exp option * exp
  withtype cmd = loc * cmd'

  type prog = cmd list

end
