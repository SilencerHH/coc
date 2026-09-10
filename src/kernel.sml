structure Kernel :> sig

  val validate : Env.env -> Syntax.prog -> unit

end = struct

  structure E = Env
  structure R = Report
  structure S = Syntax

  open Term

  fun shift d = let
    fun go c = fn
      t as Sort _ => t
      | t as Var n => if n >= c then Var (n + d) else t
      | Pi (t1, t2) => Pi (go c t1, go (c + 1) t2)
      | Lam (t1, t2) => Lam (go c t1, go (c + 1) t2)
      | App (t1, t2) => App (go c t1, go c t2)
    in go 0 end

  fun subst r = let
    fun go c = fn
      t as Sort _ => t
      | t as Var n => if n = c then shift (c + 1) r else t
      | Pi (t1, t2) => Pi (go c t1, go (c + 1) t2)
      | Lam (t1, t2) => Lam (go c t1, go (c + 1) t2)
      | App (t1, t2) => App (go c t1, go c t2)
    in shift ~1 o go 0 end

  val rec normalize = fn
    t as (Sort _ | Var _ | Pi _ | Lam _) => t
    | App (t1, t2) => (case normalize t1 of
      Lam (_, t3) => normalize (subst t2 t3)
      | t1' => App (t1', t2))

  fun equiv (t1, t2) = case (normalize t1, normalize t2) of
    (Sort s1, Sort s2) => s1 = s2
    | (Var n1, Var n2) => n1 = n2
    | (Pi (t11, t12), Pi (t21, t22)) =>
      equiv (t11, t21) andalso equiv (t12, t22)
    | (Lam (t11, t12), Lam (t21, t22)) =>
      equiv (t11, t21) andalso equiv (t12, t22)
    | (App (t11, t12), App (t21, t22)) =>
      equiv (t11, t21) andalso equiv (t12, t22)
    | _ => false

  fun infer env ctx (loc, e) = case e of
    S.Prop => (Sort Prop, Sort Type)
    | S.Var x => (case List.findi (fn (_, (y, _)) => x = y) ctx of
      SOME (n, (_, t)) => (Var n, shift (n + 1) t)
      | NONE => (case E.get (env, x) of
        SOME (E.Df {v, t}) => (v, t)
        | NONE => raise R.Unbound (loc, x)))
    | S.Pi (x, e1, e2) => (case infer env ctx e1 of
      (t1, Sort _) => (case infer env ((x, t1) :: ctx) e2 of
        (t2, u2 as Sort _) => (Pi (t1, t2), u2)
        | _ => raise R.Shape (#1 e2, "sort"))
      | _ => raise R.Shape (#1 e1, "sort"))
    | S.Lam (x, e1, e2) => (case infer env ctx e1 of
      (t1, Sort _) =>
        let val (t2, u2) = infer env ((x, t1) :: ctx) e2
        in (Lam (t1, t2), Pi (t1, u2)) end
      | _ => raise R.Shape (#1 e1, "sort"))
    | S.App (e1, e2) => (case infer env ctx e1 of
      (t1, Pi (u11, u12)) =>
        let val (t2, u2) = infer env ctx e2
        in
          if equiv (u11, u2) then
            (normalize (App (t1, t2)), normalize (subst t2 u12))
          else raise R.Mismatch (#1 e2) end
      | _ => raise R.Shape (#1 e1, "pi"))

  fun validate1 env (loc, S.Def (x, e1, e2)) =
    let
      val () = if E.has (env, x) then raise R.Duplicate (loc, x) else ()
      val t1 = Option.map (#1 o infer env []) e1
      val (v, t2) = infer env [] e2
    in case t1 of
      NONE => E.add (env, x, E.Df {v = v, t = t2})
      | SOME t1' =>
        if equiv (t1', t2) then E.add (env, x, E.Df {v = v, t = t1'})
        else raise R.Mismatch loc end

  fun validate env = app (validate1 env)

end
