structure Env :> sig

  type env

  val new : unit -> env

  val commit : env -> unit
  val rollback : env -> unit
  val reset : env -> unit

  val has : env * string -> bool
  val addAxiom : env * string * Term.term -> unit
  val addDef : env * string * {v : Term.term, t : Term.term} -> unit
  val get : env * string -> {v : Term.term, t : Term.term} option
  val listAxioms : env -> (string * Term.term) list

end = struct

  open Term

  structure M = RedBlackMapFn (

    type ord_key = string

    val compare = String.compare

  )

  datatype env = Env of (int * term * term) M.map ref * int ref

  fun new () = Env (ref M.empty, ref 0)

  fun commit (Env (_, sn)) = sn := !sn + 1

  fun rollback (Env (cs, sn)) = cs := M.filter (fn (n, _, _) => n <> !sn) (!cs)

  fun reset (Env (cs, sn)) = (cs := M.empty; sn := 0)

  fun has (Env (cs, _), k) = M.inDomain (!cs, k)

  fun addAxiom (Env (cs, sn), x, t) = cs := M.insert (!cs, x, (!sn, Axiom x, t))

  fun addDef (Env (cs, sn), x, {v, t}) =
    cs := M.insert (!cs, x, (!sn, Def (x, v), t))

  fun get (Env (cs, _), x) =
    Option.map (fn (_, v, t) => {v = v, t = t}) (M.find (!cs, x))

  fun listAxioms (Env (cs, _)) =
    M.listItemsi
      (M.mapPartial (fn (_, Axiom _, t) => SOME t | _ => NONE) (!cs))

end
