local

  datatype tag =
    (* 文字关键字 *)
    AXIOM
    | DEF
    | IN
    | LET
    | PROP
    (* 符号关键字 *)
    | MINUSGT
    (* 标识符 *)
    | ID
    (* 标点符号 *)
    | AT
    | COLONEQ
    | COLON
    | COMMA
    | LBRACE
    | LBRACK
    | LPAREN
    | RBRACE
    | RBRACK
    | RPAREN
    (* 其他 *)
    | EOF
    | ERROR

in

  structure Lex :> sig

    datatype tag = datatype tag
    type token
    type stream

    val getTag : token -> tag
    val getValue : token -> string
    val getLoc : token -> Report.loc

    val lex : string -> stream
    val peek : stream -> token
    val eat : stream -> tag -> token

  end = struct

    structure SS = Substring

    structure R = Report

    datatype tag = datatype tag
    type token = tag * substring
    type stream = substring ref

    fun getTag (tag, _) = tag
    fun getValue (_, ss) = SS.string ss
    fun getLoc (_, ss) = let val (_, i, n) = SS.base ss in (i, i + n) end

    fun skipWS ss = case SS.getc ss of
      SOME (#"#", ss') => skipWS (SS.dropl (fn c => c <> #"\n") ss')
      | SOME ((#" " | #"\n" | #"\r" | #"\t"), ss') => skipWS ss'
      | _ => ss

    fun lex s = ref (skipWS (SS.full s))

    fun cut n tag ss =
      let val (ss1, ss2) = SS.splitAt (ss, n) in ((tag, ss1), ss2) end

    fun isIdent c = Char.isAlphaNum c orelse Char.contains "_+-*/<=>\\~" c

    fun read ss = case SS.first ss of
      NONE => ((EOF, ss), ss)
      | SOME #"@" => cut 1 AT ss
      | SOME #":" =>
        if SS.isPrefix ":=" ss then cut 2 COLONEQ ss else cut 1 COLON ss
      | SOME #"," => cut 1 COMMA ss
      | SOME #"{" => cut 1 LBRACE ss
      | SOME #"[" => cut 1 LBRACK ss
      | SOME #"(" => cut 1 LPAREN ss
      | SOME #"}" => cut 1 RBRACE ss
      | SOME #"]" => cut 1 RBRACK ss
      | SOME #")" => cut 1 RPAREN ss
      | SOME _ =>
        let
          val (ss1, ss2) = SS.splitl isIdent ss
          val tag = case SS.string ss1 of
            "axiom" => AXIOM
            | "def" => DEF
            | "in" => IN
            | "let" => LET
            | "prop" => PROP
            | "->" => MINUSGT
            | "" => ERROR
            | _ => ID
        in ((tag, ss1), ss2) end

    fun peek strm = #1 (read (!strm))

    fun eat strm tag =
      let val (tok, ss) = read (!strm)
      in
        if #1 tok = tag then (strm := skipWS ss; tok)
        else raise R.Syntax (getLoc tok) end

  end

end
