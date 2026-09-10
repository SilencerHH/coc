structure Term = struct

  datatype sort = Prop | Type

  datatype term =
    Sort of sort
    | Var of int
    | Pi of term * term
    | Lam of term * term
    | App of term * term

end
