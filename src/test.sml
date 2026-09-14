structure Test :> sig end = struct

  structure C = Ctx
  structure E = Env
  structure K = Kernel
  structure P = Parse
  structure R = Report

  open Syntax

  fun runWith env src = K.validate env (P.parse src)

  fun run src = runWith (E.new ()) src

  fun fails src msg =
    (run src; raise Match)
      handle ex =>
        (R.report "" src ex
          handle ex as Fail msg' => if msg = msg' then () else raise ex)

  (***** 环境 *****)

  (* 顺序提交与重置 *)
  val () =
    let val env = E.new ()
    in
      runWith env "def x := prop";
      E.commit env;
      runWith env "def y := x";
      E.commit env;
      if E.has (env, "x") andalso E.has (env, "y") then () else raise Match;
      E.reset env;
      if not (E.has (env, "x")) andalso not (E.has (env, "y")) then ()
      else raise Match end

  (* 回滚 *)
  val () =
    let val env = E.new ()
    in
      runWith env "def x := prop";
      if E.has (env, "x") then () else raise Match;
      E.rollback env;
      runWith env "def y := prop";
      if not (E.has (env, "x")) andalso E.has (env, "y") then ()
      else raise Match;
      E.commit env;
      E.rollback env;
      runWith env "def x := y";
      if E.has (env, "x") andalso E.has (env, "y") then () else raise Match end

  (* 公理列表 *)
  val () =
    let val env = E.new ()
    in
      runWith env "axiom b : prop";
      runWith env "axiom a : b";
      runWith env "def c := a";
      runWith env "axiom d : b -> b";
      if
        E.has (env, "a") andalso E.has (env, "b")
          andalso E.has (env, "c") andalso E.has (env, "d") then ()
      else raise Match;
      case map (fn (x, t) => (x, R.show C.empty t)) (E.listAxioms env) of
        [("a", "b"), ("b", "prop"), ("d", "({$1 : b} b)")] => ()
        | _ => raise Match end

  (***** 解析 *****)

  (* 空文件 *)
  val () = case P.parse "" of [] => () | _ => raise Match

  (* 注释 *)
  val () = case P.parse "def#something\nx := prop" of
    [((0, 23), Def ("x", NONE, ((19, 23), Prop)))] => ()
    | _ => raise Match

  (* 混合标识符 *)
  val () = case P.parse "def 1->x := prop" of
    [((0, 16), Def ("1->x", NONE, ((12, 16), Prop)))] => ()
    | _ => raise Match

  (* 可省略空格 *)
  val () = case P.parse "def x:prop:=prop" of
    [((0, 16), Def ("x", SOME ((6, 10), Prop), ((12, 16), Prop)))] => ()
    | _ => raise Match

  (* 箭头右结合 *)
  val () = case P.parse "def x := prop -> prop -> prop" of
    [(_, Def (_, _,
      ((9, 29), Pi ("", (_, Prop),
        ((17, 29), Pi ("", (_, Prop), (_, Prop)))))))] => ()
    | _ => raise Match

  (* 中缀右结合 *)
  val () = case
    P.parse "def x := [a : prop] [+ : prop -> prop -> prop] a + a + a" of
    [(_, Def (_, _, (_, Lam (_, _, (_, Lam (_, _,
      ((47, 56), App (
        ((47, 50), App ((_, Var "+"), (_, Var "a"))),
        ((51, 56), App (
          ((51, 54), App ((_, Var "+"), (_, Var "a"))),
          (_, Var "a")))))))))))] => ()
    | _ => raise Match

  (* 中缀参数 *)
  val () = case
    P.parse
      "def x\n\
      \  := [a : prop] [+ : prop -> prop -> prop -> prop -> prop]\n\
      \    a +@(a, a) a" of
    [(_, Def (_, _, (_, Lam (_, _, (_, Lam (_, _,
      ((69, 81), App (
        ((69, 78), App (
          ((71, 78), App (
            ((71, 75), App (((71, 72), Var "+"), ((74, 75), Var "a"))),
            ((77, 78), Var "a"))),
          ((69, 70), Var "a"))),
        ((80, 81), Var "a")))))))))] => ()
    | _ => raise Match

  (* 语法错误 1 *)
  val () = fails "def $" ":1.5-1.5: syntax error"

  (* 语法错误 2 *)
  val () = fails "def def" ":1.5-1.8: syntax error"

  (* 语法错误 3 *)
  val () = fails "def :=" ":1.5-1.7: syntax error"

  (* 语法错误 4 *)
  val () = fails "defx:=prop" ":1.1-1.5: syntax error"

  (* 语法错误 5 *)
  val () = fails "def x := prop prop" ":1.15-1.19: syntax error"

  (* 语法错误 6 *)
  val () = fails "def x := x x" ":1.13-1.13: syntax error"

  (***** 验证 *****)

  (* 未绑定变量 *)
  val () = fails "def x := x" ":1.10-1.11: unbound id x"

  (* 重复定义 *)
  val () =
    fails "def x := prop def x := prop" ":1.15-1.28: duplicate definition of x"

  (* 类型错误 1 *)
  val () =
    fails
      "def x := {a : prop} {b : a} {c : b} c"
      ":1.34-1.35: type mismatch\nexpected (sort)\ngot      a"

  (* 类型错误 2 *)
  val () =
    fails
      "def x := {a : prop} {b : a} b"
      ":1.29-1.30: type mismatch\nexpected (sort)\ngot      a"

  (* 类型错误 3 *)
  val () =
    fails
      "def x := {a : prop} {b : a} [c : b] c"
      ":1.34-1.35: type mismatch\nexpected (sort)\ngot      a"

  (* 类型错误 4 *)
  val () =
    fails
      "def x := prop(prop)"
      ":1.10-1.14: type mismatch\nexpected (pi)\ngot      #"

  (* 类型错误 5 *)
  val () =
    fails
      "def x : prop := [a : prop] a"
      ":1.17-1.29: type mismatch\nexpected prop\ngot      (pi)"

  (* 类型错误 6 *)
  val () =
    fails
      "def x : {a : prop -> prop} prop := [a : prop] prop"
      ":1.41-1.45: type mismatch\nexpected ({$1 : prop} prop)\ngot      prop"

  (* 类型错误 7 *)
  val () =
    fails
      "def x := ([x : prop] x)(prop)"
      ":1.25-1.29: type mismatch\nexpected prop\ngot      #"

  (* 类型错误 8 *)
  val () =
    fails
      "def x := [a : prop] [b : prop] [c : a] [f : b -> b] f(c)"
      ":1.55-1.56: type mismatch\nexpected b\ngot      a"

  (* 类型错误 9 *)
  val () =
    fails
      "def x : prop := prop"
      ":1.17-1.21: type mismatch\nexpected prop\ngot      #"

  (* 类型错误 10 *)
  val () =
    fails
      "def False := {A : prop} A\n\
      \def ~ : {A : prop} A -> False := [A : prop] A -> False"
      ":2.45-2.55: type mismatch\n\
      \expected ({$1 : A} False)\n\
      \got      prop"

  (* 类型错误 11 *)
  val () =
    fails
      "def False := {A : prop} A\n\
      \def True := False -> False\n\
      \def triv : True := [h : False] h\n\
      \def x : False := triv"
      ":4.18-4.22: type mismatch\n\
      \expected False\n\
      \got      True"

  (* 类型错误 12 *)
  val () =
    fails
      "axiom a : prop axiom b : a axiom c : b"
      ":1.38-1.39: type mismatch\nexpected (sort)\ngot      a"

  (* 无法推断 1 *)
  val () = fails "def x := [x] x" ":1.10-1.15: cannot infer type of x"

  (* 无法推断 2 *)
  val () = fails "def x := ?" ":1.10-1.11: cannot infer type of ?"

  (* 洞 *)
  val () =
    fails
      "def x : {A : prop} A -> A := [A] [a] let b := [x : A] x in ?"
      ":1.60-1.61: hole\n\
      \A : prop\n\
      \a : A\n\
      \b : ({$1 : A} A) := ([$1 : A] $1)\n\
      \expected A"

  (* 变量遮蔽 *)
  val () =
    run
      "axiom A : prop\n\
      \axiom B : prop\n\
      \axiom a : A\n\
      \axiom b : B\n\
      \def 1 := [a : A] [a : B] a\n\
      \def 1+ : A -> B -> B := 1\n\
      \def 2 := let a := a in let a := b in a\n\
      \def 2+ : B := 2"

  (* 类型判等 *)
  val () =
    run
      "axiom a : prop\n\
      \axiom b : a\n\
      \def x := let c := a in let d : c := b in ([x : c] x)(b)"

  (* 参数类型推断 *)
  val () =
    run
      "def x : {A : prop} A -> A\n\
      \  := [A] let _ := ([x : A -> A] x)([x] x) in [a] a"

  (* 类型位置 let *)
  val () =
    run
      "def x : let t := {A : prop} A -> A in t\n\
      \  := [A] [a] let x : let B := A in B := a in x"

  (* 编码自然数 *)
  val () =
    run
      "def Nat := {A : prop} A -> (A -> A) -> A\n\
      \def 1 : Nat := [A : prop] [z : A] [s : A -> A] s(z)\n\
      \def 2 : Nat := [A] [z] [s] s(s(z))\n\
      \def + : Nat -> Nat -> Nat\n\
      \  := [m : Nat] [n : Nat] [A : prop] [z : A] [s : A -> A]\n\
      \    m(A, n(A, z, s), s)\n\
      \def = : {A : prop} A -> A -> prop\n\
      \  := [A : prop] [x : A] [y : A] {P : A -> prop} P(x) -> P(y)\n\
      \def refl : {A : prop} {x : A} =(A, x, x)\n\
      \  := [A : prop] [x : A] [P : A -> prop] [h : P(x)] h\n\
      \def 1+1=2 : =(Nat, +(1, 1), 2) := refl(Nat, 2)"

end
