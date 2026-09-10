structure Syntax = struct

  type loc = Report.loc

  datatype exp' =
    Prop
    | Var of string
    | Pi of string * exp * exp
    | Lam of string * exp * exp
    | App of exp * exp
  withtype exp = loc * exp'

  datatype cmd' = Def of string * exp option * exp
  withtype cmd = loc * cmd'

  type prog = cmd list

end
