structure Report :> sig

  type loc = int * int

  exception Syntax of loc
  exception Unbound of loc * string
  exception Duplicate of loc * string
  exception Mismatch of loc * string * string
  exception Infer of loc * string

  val show : Ctx.ctx -> Term.term -> string
  val report : string -> string -> exn -> 'a

end = struct

  structure C = Ctx

  open Term

  type loc = int * int

  exception Syntax of loc
  exception Unbound of loc * string
  exception Duplicate of loc * string
  exception Mismatch of loc * string * string
  exception Infer of loc * string

  fun show ctx t =
    let
      val r = ref 1
      fun fresh () = "$" ^ Int.toString (!r) before r := !r + 1
      fun go ctx = fn
        Sort Prop => "prop"
        | Sort Type => "#"
        | (Axiom x | Def (x, _)) => x
        | Var n => #x (C.index (ctx, n))
        | Pi (t1, t2) =>
          let val x = fresh ()
          in
            "{" ^ x ^ " : " ^ go ctx t1 ^ "} "
              ^ go (C.add (ctx, {x = x, v = NONE, t = t1})) t2 end
        | Lam (t1, t2) =>
          let val x = fresh ()
          in
            "[" ^ x ^ " : " ^ go ctx t1 ^ "] "
              ^ go (C.add (ctx, {x = x, v = NONE, t = t1})) t2 end
        | App (t1, t2) => go ctx t1 ^ "(" ^ go ctx t2 ^ ")"
    in go ctx t end

  fun locate src pos =
    let
      val lines = String.fields (fn c => c = #"\n") (substring (src, 0, pos))
      val ln = length lines
      val cn = size (List.last lines) + 1
    in Int.toString ln ^ "." ^ Int.toString cn end

  fun report filename src ex =
    let
      fun report' (pos1, pos2) msg =
        raise Fail
          (filename ^ ":" ^ locate src pos1 ^ "-" ^ locate src pos2 ^ ": "
            ^ msg)
    in case ex of
      Syntax loc => report' loc "syntax error"
      | Unbound (loc, x) => report' loc ("unbound id " ^ x)
      | Duplicate (loc, x) => report' loc ("duplicate definition of " ^ x)
      | Mismatch (loc, t1, t2) =>
        report' loc ("type mismatch\nexpected " ^ t1 ^ "\ngot      " ^ t2)
      | Infer (loc, x) => report' loc ("cannot infer type of " ^ x)
      | _ => raise ex end

end
