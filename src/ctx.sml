structure Ctx :> sig

  type entry = {x : string, v : Term.term option, t : Term.term}
  type ctx

  val empty : ctx
  val add : ctx * entry -> ctx
  val get : ctx * string -> (int * entry) option
  val index : ctx * int -> entry

end = struct

  type entry = {x : string, v : Term.term option, t : Term.term}
  type ctx = entry list

  val empty = []

  fun add (ctx, entry) = entry :: ctx

  fun get (ctx : ctx, x) = List.findi (fn (_, {x = y, ...}) => x = y) ctx

  val index = List.nth

end
