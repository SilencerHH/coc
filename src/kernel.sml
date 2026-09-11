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
          | _ => raise R.Mismatch (#1 e1, "(sort)", R.show ctx u1)
        val ctx' = (x, t1) :: ctx
        val (t2, u2) = infer env ctx' e2
        val () = case normalize env u2 of
          Sort _ => ()
          | _ => raise R.Mismatch (#1 e2, "(sort)", R.show ctx' u2)
      in (Pi (t1, t2), u2) end
    | S.Lam (x, NONE, _) => raise R.Infer (loc, x)
    | S.Lam (x, SOME e1, e2) =>
      let
        val (t1, u1) = infer env ctx e1
        val () = case normalize env u1 of
          Sort _ => ()
          | _ => raise R.Mismatch (#1 e1, "(sort)", R.show ctx u1)
        val (t2, u2) = infer env ((x, t1) :: ctx) e2
      in (Lam (t1, t2), Pi (t1, u2)) end
    | S.App (e1, e2) =>
      let
        val (t1, u1) = infer env ctx e1
        val (u11, u12) = case normalize env u1 of
          Pi us => us
          | _ => raise R.Mismatch (#1 e1, "(pi)", R.show ctx u1)
        val t2 = check env ctx u11 e2
      in (App (t1, t2), subst t2 u12) end

  and check env ctx u (loc, e) = case e of
    S.Lam (x, e1, e2) =>
      let
        val (u1, u2) = case normalize env u of
          Pi us => us
          | _ => raise R.Mismatch (loc, R.show ctx u, "(pi)")
        val t1 = case e1 of
          NONE => u1
          | SOME e1' =>
            let val (t1, _) = infer env ctx e1'
            in
              if equiv env (u1, t1) then t1
              else raise R.Mismatch (#1 e1', R.show ctx u1, R.show ctx t1) end
        val t2 = check env ((x, t1) :: ctx) u2 e2
      in Lam (t1, t2) end
    | _ =>
      let val (t, u') = infer env ctx (loc, e)
      in
        if equiv env (u, u') then t
        else raise R.Mismatch (loc, R.show ctx u, R.show ctx u') end

  fun validate1 env (loc, c) = case c of
    S.Def (x, NONE, e) =>
      let
        val () = if E.has (env, x) then raise R.Duplicate (loc, x) else ()
        val (t, u) = infer env [] e
      in E.add (env, x, E.Df {v = t, t = u}) end
    | S.Def (x, SOME e1, e2) =>
      let
        val () = if E.has (env, x) then raise R.Duplicate (loc, x) else ()
        val (t1, _) = infer env [] e1
        val t2 = check env [] t1 e2
      in E.add (env, x, E.Df {v = t2, t = t1}) end

  fun validate env = app (validate1 env)

end
