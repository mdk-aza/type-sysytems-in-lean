import TypeSystemsInLean.PLFABased.Syntax

/-!
# Typing

This file defines the typing rules of the Simply Typed Lambda Calculus (STLC).

The typing relation assigns a type to each well-formed term
under a typing context.

This corresponds to the typing judgment

    Γ ⊢ t : A

in the PLFA Lambda chapter.
-/

/-!
# 型付け

このファイルでは Simply Typed Lambda Calculus (STLC)
の型付け規則を定義する。

型付けとは

    「この項はどの型を持つか」

を形式的に表す規則である。

PLFA の Lambda 章における

    Γ ⊢ t : A

に対応する。
-/

namespace STLC

open Term

------------------------------------------------------------
-- Types
------------------------------------------------------------

/--
Simple types.

A type is either

* a base type
* a function type
-/

/-
単純型。

型は

* 基本型
* 関数型

の2種類からなる。
-/
inductive Ty where
| base : Ty
| arr : Ty → Ty → Ty
deriving DecidableEq, Repr

infixr:60 " ⇒ " => Ty.arr

------------------------------------------------------------
-- Typing Context
------------------------------------------------------------

/--
Typing contexts.

Because terms use de Bruijn indices,
a context is represented as a list of types.

The head of the list corresponds to variable #0.
-/

/-
型環境。

de Bruijn index を用いるため、
型環境は型のリストで表現する。

先頭要素が

    #0

に対応する。
-/
abbrev Context := List Ty

/--
Lookup a variable in the typing context.
-/

/-
型環境から変数の型を取得する。

例：

    [A, B, C]

なら

    #0 ↦ A
    #1 ↦ B
    #2 ↦ C
-/
def lookup : Context → Index → Option Ty
| [], _ =>
    none

| A :: _, 0 =>
    some A

| _ :: Γ, n + 1 =>
    lookup Γ n

------------------------------------------------------------
-- Typing Relation
------------------------------------------------------------

/--
Typing judgment.

    Γ ⊢ t : A

means that

term t has type A
under typing context Γ.
-/

/-
型付け関係。

    Γ ⊢ t : A

とは

「型環境 Γ のもとで、
項 t は型 A を持つ」

ことを表す。

これは STLC の最も基本となる推論規則である。
-/
inductive HasType : Context → Term → Ty → Prop where

/--
Variable rule.
-/

/-
変数規則。

型環境から対応する型を取り出す。

推論規則：

        Γ(x)=A
    ----------------
      Γ ⊢ x : A
-/
| var
    {Γ : Context}
    {x : Index}
    {A : Ty}
    :
    lookup Γ x = some A →
    HasType Γ (#x) A

/--
Lambda abstraction.
-/

/-
ラムダ抽象。

ラムダ内部では新しい変数が束縛されるため、
型環境の先頭に引数型を追加する。

推論規則：

      A::Γ ⊢ t : B
    -------------------
     Γ ⊢ λt : A ⇒ B
-/
| lam
    {Γ : Context}
    {A B : Ty}
    {t : Term}
    :
    HasType (A :: Γ) t B →
    HasType Γ (ƛ t) (A ⇒ B)

/--
Application.
-/

/-
関数適用。

関数が

    A ⇒ B

型を持ち、

引数が

    A

型を持てば、

適用結果は

    B

型になる。

推論規則：

    Γ ⊢ t : A⇒B
    Γ ⊢ u : A
    ----------------
      Γ ⊢ t u : B
-/
| ap
    {Γ : Context}
    {t u : Term}
    {A B : Ty}
    :
    HasType Γ t (A ⇒ B) →
    HasType Γ u A →
    HasType Γ (t □ u) B

------------------------------------------------------------
-- Notation
------------------------------------------------------------

/--
Typing notation.

Allows writing

    Γ ⊢ t : A

instead of

    HasType Γ t A.
-/

/-
型付け記法。

HasType を

    Γ ⊢ t : A

という数学的な表記で書けるようにする。
-/
notation:50 Γ " ⊢ " t " : " A =>
  HasType Γ t A

------------------------------------------------------------
-- Examples
------------------------------------------------------------

/--
The identity function has type

    base ⇒ base.
-/

/-
恒等関数

    λx.x

は

    base ⇒ base

型を持つ。
-/
example :
    [] ⊢ (ƛ #0) : (Ty.base ⇒ Ty.base) := by
  apply HasType.lam
  apply HasType.var
  rfl

end STLC