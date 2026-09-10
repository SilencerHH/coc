structure Parse :> sig

  val parse : string -> Syntax.prog

end = struct

  open Lex
  open Syntax

  val mkApp = foldl (fn (e2, e1) => ((#1 (#1 e1), #2 (#1 e2)), App (e1, e2)))

  fun exp strm = infixexp strm (prefixexp strm)

  and prefixexp strm = case getTag (peek strm) of
    PROP => (getLoc (eat strm PROP), Prop)
    | ID => let val tok = eat strm ID in (getLoc tok, Var (getValue tok)) end
    | LBRACE =>
      let
        val pos1 = #1 (getLoc (eat strm LBRACE))
        val x = getValue (eat strm ID)
        val _ = eat strm COLON
        val e1 = exp strm
        val _ = eat strm RBRACE
        val e2 = exp strm
      in ((pos1, #2 (#1 e2)), Pi (x, e1, e2)) end
    | LBRACK =>
      let
        val pos1 = #1 (getLoc (eat strm LBRACK))
        val x = getValue (eat strm ID)
        val _ = eat strm COLON
        val e1 = exp strm
        val _ = eat strm RBRACK
        val e2 = exp strm
      in ((pos1, #2 (#1 e2)), Lam (x, e1, e2)) end
    | _ =>
      let
        val _ = eat strm LPAREN
        val e = exp strm
        val _ = eat strm RPAREN
      in e end

  and infixexp strm e = case getTag (peek strm) of
    LPAREN =>
      let
        val _ = eat strm LPAREN
        val es = args strm
        val _ = eat strm RPAREN
      in infixexp strm (mkApp e es) end
    | MINUSGT =>
      let
        val _ = eat strm MINUSGT
        val e2 = exp strm
      in ((#1 (#1 e), #2 (#1 e2)), Pi ("", e, e2)) end
    | _ => e

  and args strm =
    let
      val e = exp strm
      fun go es = case getTag (peek strm) of
        RPAREN => rev es
        | _ => (eat strm COMMA; go (exp strm :: es))
    in go [e] end

  fun cmd strm =
    let
      val pos1 = #1 (getLoc (eat strm DEF))
      val x = getValue (eat strm ID)
      val e1 = case getTag (peek strm) of
        COLON => (eat strm COLON; SOME (exp strm))
        | _ => NONE
      val _ = eat strm COLONEQ
      val e2 = exp strm
    in ((pos1, #2 (#1 e2)), Def (x, e1, e2)) end

  fun prog strm =
    let
      fun go cs = case getTag (peek strm) of
        EOF => rev cs
        | _ => go (cmd strm :: cs)
    in go [] end

  fun parse s = prog (lex s)

end
