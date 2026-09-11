structure Report :> sig

  type loc = int * int

  exception Syntax of loc
  exception Unbound of loc * string
  exception Duplicate of loc * string
  exception Shape of loc * (string * Term.term) list * string * Term.term
  exception Mismatch of loc * (string * Term.term) list * Term.term * Term.term

  val report : string -> string -> exn -> 'a

end = struct

  open Term

  type loc = int * int

  exception Syntax of loc
  exception Unbound of loc * string
  exception Duplicate of loc * string
  exception Shape of loc * (string * Term.term) list * string * Term.term
  exception Mismatch of loc * (string * Term.term) list * Term.term * Term.term

  fun show ctx t =
    let
      val r = ref 1
      fun fresh () = "$" ^ Int.toString (!r) before r := !r + 1
      fun go ctx = fn
        Sort Prop => "prop"
        | Sort Type => "#"
        | Const x => x
        | Var n => (#1 o #2 o valOf o List.findi (fn (m, _) => m = n)) ctx
        | Pi (t1, t2) =>
          let val x = fresh ()
          in "{" ^ x ^ " : " ^ go ctx t1 ^ "} " ^ go ((x, t1) :: ctx) t2 end
        | Lam (t1, t2) =>
          let val x = fresh ()
          in "[" ^ x ^ " : " ^ go ctx t1 ^ "] " ^ go ((x, t1) :: ctx) t2 end
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
      | Shape (loc, ctx, x, t) =>
        report' loc ("expected term of " ^ x ^ "\ngot " ^ show ctx t)
      | Mismatch (loc, ctx, t1, t2) =>
        report'
          loc
          ("type mismatch\nexpected " ^ show ctx t1
            ^ "\ngot      " ^ show ctx t2)
      | _ => raise ex end

end
