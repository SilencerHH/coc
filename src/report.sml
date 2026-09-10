structure Report :> sig

  type loc = int * int

  exception Syntax of loc
  exception Unbound of loc * string
  exception Duplicate of loc * string
  exception Shape of loc * string
  exception Mismatch of loc

  val report : string -> string -> exn -> 'a

end = struct

  type loc = int * int

  exception Syntax of loc
  exception Unbound of loc * string
  exception Duplicate of loc * string
  exception Shape of loc * string
  exception Mismatch of loc

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
      | Shape (loc, x) => report' loc ("expected term of " ^ x)
      | Mismatch loc => report' loc "type mismatch"
      | _ => raise ex end

end
