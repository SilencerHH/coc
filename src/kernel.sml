structure Kernel :> sig

  val validate : Env.env -> Syntax.prog -> unit

end = struct

  structure C = Ctx
  structure E = Env
  structure R = Report
  structure S = Syntax

  open Term

  fun shift d = let
    fun go c = fn
      t as (Sort _ | Axiom _ | Def _) => t
      | t as Var n => if n >= c then Var (n + d) else t
      | Pi (t1, t2) => Pi (go c t1, go (c + 1) t2)
      | Lam (t1, t2) => Lam (go c t1, go (c + 1) t2)
      | App (t1, t2) => App (go c t1, go c t2)
    in go 0 end

  fun subst r = let
    fun go c = fn
      t as (Sort _ | Axiom _ | Def _) => t
      | t as Var n => if n = c then shift (c + 1) r else t
      | Pi (t1, t2) => Pi (go c t1, go (c + 1) t2)
      | Lam (t1, t2) => Lam (go c t1, go (c + 1) t2)
      | App (t1, t2) => App (go c t1, go c t2)
    in shift ~1 o go 0 end

  val rec normalize = fn
    t as (Sort _ | Axiom _ | Var _ | Pi _ | Lam _) => t
    | Def (_, t) => normalize t
    | App (t1, t2) => (case normalize t1 of
      Lam (_, t3) => normalize (subst t2 t3)
      | t1' => App (t1', t2))

  fun equiv (t1, t2) = case (normalize t1, normalize t2) of
    (Sort s1, Sort s2) => s1 = s2
    | (Axiom x1, Axiom x2) => x1 = x2
    | ((Def _, _) | (_, Def _)) => raise Match
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
    | S.Var x => (case C.get (ctx, x) of
      SOME (n, {v = NONE, t, ...}) => (Var n, shift (n + 1) t)
      | SOME (n, {v = SOME v, t, ...}) => (shift (n + 1) v, shift (n + 1) t)
      | NONE => (case E.get (env, x) of
        SOME {v, t} => (v, t)
        | NONE => raise R.Unbound (loc, x)))
    | S.Pi (x, e1, e2) =>
      let
        val (t1, u1) = infer env ctx e1
        val () = case normalize u1 of
          Sort _ => ()
          | _ => raise R.Mismatch (#1 e1, "(sort)", R.show ctx u1)
        val ctx' = C.add (ctx, {x = x, v = NONE, t = t1})
        val (t2, u2) = infer env ctx' e2
        val () = case normalize u2 of
          Sort _ => ()
          | _ => raise R.Mismatch (#1 e2, "(sort)", R.show ctx' u2)
      in (Pi (t1, t2), u2) end
    | S.Lam (x, NONE, _) => raise R.Infer (loc, x)
    | S.Lam (x, SOME e1, e2) =>
      let
        val (t1, u1) = infer env ctx e1
        val () = case normalize u1 of
          Sort _ => ()
          | _ => raise R.Mismatch (#1 e1, "(sort)", R.show ctx u1)
        val (t2, u2) = infer env (C.add (ctx, {x = x, v = NONE, t = t1})) e2
      in (Lam (t1, t2), Pi (t1, u2)) end
    | S.App (e1, e2) =>
      let
        val (t1, u1) = infer env ctx e1
        val (u11, u12) = case normalize u1 of
          Pi us => us
          | _ => raise R.Mismatch (#1 e1, "(pi)", R.show ctx u1)
        val t2 = check env ctx u11 e2
      in (App (t1, t2), subst t2 u12) end
    | S.Let (x, e1, e2, e3) =>
      let
        val (t2, u2) = inferWith env ctx e1 e2
        val (t3, u3) = infer env (C.add (ctx, {x = x, v = SOME t2, t = u2})) e3
      in (shift ~1 t3, shift ~1 u3) end
    | S.Hole => raise R.Infer (loc, "?")

  and check env ctx u (loc, e) = case e of
    S.Lam (x, e1, e2) =>
      let
        val (u1, u2) = case normalize u of
          Pi us => us
          | _ => raise R.Mismatch (loc, R.show ctx u, "(pi)")
        val t1 = case e1 of
          NONE => u1
          | SOME e1' =>
            let val (t1, _) = infer env ctx e1'
            in
              if equiv (u1, t1) then t1
              else raise R.Mismatch (#1 e1', R.show ctx u1, R.show ctx t1) end
        val t2 = check env (C.add (ctx, {x = x, v = NONE, t = t1})) u2 e2
      in Lam (t1, t2) end
    | S.Let (x, e1, e2, e3) =>
      let
        val (t2, u2) = inferWith env ctx e1 e2
        val t3 =
          check env (C.add (ctx, {x = x, v = SOME t2, t = u2})) (shift 1 u) e3
      in shift ~1 t3 end
    | S.Hole => raise R.Hole (loc, ctx, u)
    | _ =>
      let val (t, u') = infer env ctx (loc, e)
      in
        if equiv (u, u') then t
        else raise R.Mismatch (loc, R.show ctx u, R.show ctx u') end

  and inferWith env ctx e1 e2 = case e1 of
    NONE => infer env ctx e2
    | SOME e1' =>
      let
        val (t1, _) = infer env ctx e1'
        val t2 = check env ctx t1 e2
      in (t2, t1) end

  fun validate1 env (loc, c) = case c of
    S.Axiom (x, e) =>
      let
        val () = if E.has (env, x) then raise R.Duplicate (loc, x) else ()
        val (t, u) = infer env C.empty e
        val () = case normalize u of
          Sort _ => ()
          | _ => raise R.Mismatch (#1 e, "(sort)", R.show C.empty u)
      in E.addAxiom (env, x, t) end
    | S.Def (x, e1, e2) =>
      let
        val () = if E.has (env, x) then raise R.Duplicate (loc, x) else ()
        val (t2, u2) = inferWith env C.empty e1 e2
      in E.addDef (env, x, {v = t2, t = u2}) end

  fun validate env = app (validate1 env)

end
