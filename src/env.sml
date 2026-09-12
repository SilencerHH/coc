structure Env :> sig

  datatype entry = Ax of Term.term | Df of {v : Term.term, t : Term.term}
  type env

  val new : unit -> env
  val commit : env -> unit
  val rollback : env -> unit
  val reset : env -> unit
  val has : env * string -> bool
  val add : env * string * entry -> unit
  val get : env * string -> entry option

end = struct

  structure T = Term

  structure M = RedBlackMapFn (

    type ord_key = string

    val compare = String.compare

  )

  datatype entry = Ax of T.term | Df of {v : T.term, t : T.term}
  datatype env = Env of (int * entry) M.map ref * int ref

  fun new () = Env (ref M.empty, ref 0)

  fun commit (Env (_, sn)) = sn := !sn + 1

  fun rollback (Env (cs, sn)) = cs := M.filter (fn (n, _) => n <> !sn) (!cs)

  fun reset (Env (cs, sn)) = (cs := M.empty; sn := 0)

  fun has (Env (cs, _), k) = M.inDomain (!cs, k)

  fun add (Env (cs, sn), k, v) = cs := M.insert (!cs, k, (!sn, v))

  fun get (Env (cs, _), k) = Option.map #2 (M.find (!cs, k))

end
