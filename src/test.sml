structure Test :> sig end = struct

  structure E = Env
  structure K = Kernel
  structure P = Parse
  structure R = Report

  open Syntax

  (***** 环境 *****)

  (* 顺序提交与重置 *)
  val () =
    let val env = E.new ()
    in
      K.validate env (P.parse "def x := prop");
      E.commit env;
      K.validate env (P.parse "def y := x");
      E.commit env;
      if E.has (env, "x") andalso E.has (env, "y") then () else raise Match;
      E.reset env;
      if not (E.has (env, "x")) andalso not (E.has (env, "y")) then ()
      else raise Match end

  (* 回滚 *)
  val () =
    let val env = E.new ()
    in
      K.validate env (P.parse "def x := prop");
      if E.has (env, "x") then () else raise Match;
      E.rollback env;
      K.validate env (P.parse "def y := prop");
      if not (E.has (env, "x")) andalso E.has (env, "y") then ()
      else raise Match;
      E.commit env;
      E.rollback env;
      K.validate env (P.parse "def x := y");
      if E.has (env, "x") andalso E.has (env, "y") then () else raise Match end

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
  val () = (P.parse "def $"; raise Match) handle R.Syntax (4, 4) => ()

  (* 语法错误 2 *)
  val () = (P.parse "def def"; raise Match) handle R.Syntax (4, 7) => ()

  (* 语法错误 3 *)
  val () = (P.parse "def :="; raise Match) handle R.Syntax (4, 6) => ()

  (* 语法错误 4 *)
  val () = (P.parse "defx:=prop"; raise Match) handle R.Syntax (0, 4) => ()

  (* 语法错误 5 *)
  val () =
    (P.parse "def x := prop prop"; raise Match) handle R.Syntax (14, 18) => ()

  (* 语法错误 6 *)
  val () =
    (P.parse "def x := x x"; raise Match) handle R.Syntax (12, 12) => ()

  (***** 验证 *****)

  (* 未绑定变量 *)
  val () =
    (K.validate (E.new ()) (P.parse "def x := x"); raise Match)
      handle R.Unbound ((9, 10), "x") => ()

  (* 重复定义 *)
  val () =
    (K.validate (E.new ()) (P.parse "def x := prop def x := prop"); raise Match)
      handle R.Duplicate ((14, 27), "x") => ()

  (* 类型错误 1 *)
  val () =
    (K.validate (E.new ()) (P.parse "def x := {a : prop} {b : a} {c : b} c");
      raise Match)
      handle R.Shape ((33, 34), "sort") => ()

  (* 类型错误 2 *)
  val () =
    (K.validate (E.new ()) (P.parse "def x := {a : prop} {b : a} b");
      raise Match)
      handle R.Shape ((28, 29), "sort") => ()

  (* 类型错误 3 *)
  val () =
    (K.validate (E.new ()) (P.parse "def x := {a : prop} {b : a} [c : b] c");
      raise Match)
      handle R.Shape ((33, 34), "sort") => ()

  (* 类型错误 4 *)
  val () =
    (K.validate (E.new ()) (P.parse "def x := prop(prop)"); raise Match)
      handle R.Shape ((9, 13), "pi") => ()

  (* 类型错误 5 *)
  val () =
    (K.validate (E.new ()) (P.parse "def x := ([x : prop] x)(prop)");
      raise Match)
      handle R.Mismatch (24, 28) => ()

  (* 类型错误 6 *)
  val () =
    (K.validate
      (E.new ())
      (P.parse "def x := [a : prop] [b : prop] [c : a] [f : b -> b] f(c)");
      raise Match)
      handle R.Mismatch (54, 55) => ()

  (* 类型错误 7 *)
  val () =
    (K.validate (E.new ()) (P.parse "def x : prop := prop"); raise Match)
      handle R.Mismatch (0, 20) => ()

  (* 编码自然数 *)
  val () =
    K.validate
      (E.new ())
      (P.parse
        "def Nat := {A : prop} A -> (A -> A) -> A\n\
        \def 1 : Nat := [A : prop] [z : A] [s : A -> A] s(z)\n\
        \def 2 : Nat := [A : prop] [z : A] [s : A -> A] s(s(z))\n\
        \def + : Nat -> Nat -> Nat\n\
        \  := [m : Nat] [n : Nat] [A : prop] [z : A] [s : A -> A]\n\
        \    m(A, n(A, z, s), s)\n\
        \def = : {A : prop} A -> A -> prop\n\
        \  := [A : prop] [x : A] [y : A] {P : A -> prop} P(x) -> P(y)\n\
        \def refl : {A : prop} {x : A} =(A, x, x)\n\
        \  := [A : prop] [x : A] [P : A -> prop] [h : P(x)] h\n\
        \def 1+1=2 : =(Nat, +(1, 1), 2) := refl(Nat, 2)")

end
