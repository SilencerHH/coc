structure Kernel :> sig

  val validate : Env.env -> Syntax.prog -> unit

end = struct

  structure E = Env
  structure R = Report
  structure S = Syntax

  open Term

  fun shift d = let
    fun go c = fn
      t as (Sort _ | Const _) => t
      | t as Var n => if n >= c then Var (n + d) else t
      | Pi (t1, t2) => Pi (go c t1, go (c + 1) t2)
      | Lam (t1, t2) => Lam (go c t1, go (c + 1) t2)
      | App (t1, t2) => App (go c t1, go c t2)
    in go 0 end

  fun subst r = let
    fun go c = fn
      t as (Sort _ | Const _) => t
      | t as Var n => if n = c then shift (c + 1) r else t
      | Pi (t1, t2) => Pi (go c t1, go (c + 1) t2)
      | Lam (t1, t2) => Lam (go c t1, go (c + 1) t2)
      | App (t1, t2) => App (go c t1, go c t2)
    in shift ~1 o go 0 end

  fun normalize env = fn
    t as (Sort _ | Var _ | Pi _ | Lam _) => t
    | Const x =>
      let val E.Df {v, ...} = valOf (E.get (env, x)) in normalize env v end
    | App (t1, t2) => (case normalize env t1 of
      Lam (_, t3) => normalize env (subst t2 t3)
      | t1' => App (t1', t2))

  fun equiv env (t1, t2) = case (normalize env t1, normalize env t2) of
    (Sort s1, Sort s2) => s1 = s2
    | ((Const _, _) | (_, Const _)) => raise Match
    | (Var n1, Var n2) => n1 = n2
    | (Pi (t11, t12), Pi (t21, t22)) =>
      equiv env (t11, t21) andalso equiv env (t12, t22)
    | (Lam (t11, t12), Lam (t21, t22)) =>
      equiv env (t11, t21) andalso equiv env (t12, t22)
    | (App (t11, t12), App (t21, t22)) =>
      equiv env (t11, t21) andalso equiv env (t12, t22)
    | _ => false

  fun infer env ctx (loc, e) = case e of
    S.Prop => (Sort Prop, Sort Type)
    | S.Var x => (case List.findi (fn (_, (y, _)) => x = y) ctx of
      SOME (n, (_, t)) => (Var n, shift (n + 1) t)
      | NONE => (case E.get (env, x) of
        SOME (E.Df {t, ...}) => (Const x, t)
        | NONE => raise R.Unbound (loc, x)))
    | S.Pi (x, e1, e2) =>
      let
        val (t1, u1) = infer env ctx e1
        val () = case normalize env u1 of
          Sort _ => ()
          | _ => raise R.Shape (#1 e1, ctx, "sort", u1)
        val (t2, u2) = infer env ((x, t1) :: ctx) e2
        val () = case normalize env u2 of
          Sort _ => ()
          | _ => raise R.Shape (#1 e2, (x, t1) :: ctx, "sort", u2)
      in (Pi (t1, t2), u2) end
    | S.Lam (x, e1, e2) =>
      let
        val (t1, u1) = infer env ctx e1
        val () = case normalize env u1 of
          Sort _ => ()
          | _ => raise R.Shape (#1 e1, ctx, "sort", u1)
        val (t2, u2) = infer env ((x, t1) :: ctx) e2
      in (Lam (t1, t2), Pi (t1, u2)) end
    | S.App (e1, e2) =>
      let
        val (t1, u1) = infer env ctx e1
        val (u11, u12) = case normalize env u1 of
          Pi us => us
          | _ => raise R.Shape (#1 e1, ctx, "pi", u1)
        val (t2, u2) = infer env ctx e2
      in
        if equiv env (u11, u2) then (App (t1, t2), subst t2 u12)
        else raise R.Mismatch (#1 e2, ctx, u11, u2) end

  fun validate1 env (loc, S.Def (x, e1, e2)) =
    let
      val () = if E.has (env, x) then raise R.Duplicate (loc, x) else ()
      val t1 = Option.map (#1 o infer env []) e1
      val (v, t2) = infer env [] e2
    in case t1 of
      NONE => E.add (env, x, E.Df {v = v, t = t2})
      | SOME t1' =>
        if equiv env (t1', t2) then E.add (env, x, E.Df {v = v, t = t1'})
        else raise R.Mismatch (loc, [], t1', t2) end

  fun validate env = app (validate1 env)

end
