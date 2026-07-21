import TypeSystemsInLean.PLFABasedSTLC.Syntax

/-!
# Typing

This file defines the typing rules of the Simply Typed Lambda Calculus (STLC).

Typing determines whether a term is well-formed with respect to
a typing context, and assigns a type to every well-typed term.

This corresponds to the typing judgment

    Γ ⊢ t : A

in the PLFA Lambda chapter.
-/

/-!
# 型付け

このファイルでは Simply Typed Lambda Calculus (STLC)
の型付け規則を定義する。

型付けとは、

「ある項が型環境のもとでどの型を持つか」

を形式的に表す推論規則である。

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

Because terms are represented using de Bruijn indices,
a typing context is simply a list of types.

The head of the list corresponds to variable #0.
-/

/-
型環境。

de Bruijn index を用いるため、
型環境は型のリストで表現する。

リストの先頭が

    #0

に対応する。
-/
abbrev Context := List Ty

------------------------------------------------------------
-- Variable Membership
------------------------------------------------------------

/--
Variable membership in a typing context.

The judgment

    Γ ∋ x : A

states that the variable represented by the
de Bruijn index `x`
has type `A` in the context `Γ`.

Unlike a lookup function, this is defined as an
inductive relation, making proofs by induction
much simpler.
-/

/-
型環境における変数所属関係。

判断

    Γ ∋ x : A

は、

de Bruijn index x が
型環境 Γ の中で
型 A を持つことを表す。

lookup 関数ではなく、
帰納的関係として定義することで、
型付けの証明が容易になる。
-/
inductive Lookup : Context → Index → Ty → Prop where

/--
The most recently bound variable.

Inference rule

    ----------------
    A :: Γ ∋ 0 : A
-/

/-
一番内側で束縛された変数。

推論規則

    ----------------
    A :: Γ ∋ 0 : A
-/
| here
    {Γ : Context}
    {A : Ty}
    :
    Lookup (A :: Γ) 0 A

/--
A variable outside the newest binding.

Inference rule

      Γ ∋ x : A
    -----------------
    B :: Γ ∋ x+1 : A
-/

/-
外側の変数。

新しい束縛を追加すると、
既存の変数は1つ外側へ移動する。

推論規則

      Γ ∋ x : A
    -----------------
    B :: Γ ∋ x+1 : A
-/
| there
    {Γ : Context}
    {A B : Ty}
    {x : Index}
    :
    Lookup Γ x A →
    Lookup (B :: Γ) (x + 1) A

notation:50 Γ " ∋ " x " : " A =>
  Lookup Γ x A

------------------------------------------------------------
-- Typing Relation
------------------------------------------------------------

/--
Typing judgment.

The judgment

    Γ ⊢ t : A

means that

the term `t`
has type `A`
under the typing context `Γ`.

This is the fundamental typing relation
of the Simply Typed Lambda Calculus.
-/

/-
型付け関係。

判断

    Γ ⊢ t : A

は、

型環境 Γ のもとで
項 t が型 A を持つことを表す。

これは STLC の中心となる
型付け関係である。
-/
inductive HasType : Context → Term → Ty → Prop where

/--
Variable rule.

Inference rule

      Γ ∋ x : A
    --------------
    Γ ⊢ #x : A
-/

/-
変数規則。

型環境に登録された型を
そのまま利用する。

推論規則

      Γ ∋ x : A
    --------------
    Γ ⊢ #x : A
-/
| var
    {Γ : Context}
    {x : Index}
    {A : Ty}
    :
    Lookup Γ x A →
    HasType Γ (#x) A

/--
Lambda abstraction.

Inference rule

    A :: Γ ⊢ t : B
    --------------------
    Γ ⊢ λt : A ⇒ B
-/

/-
ラムダ抽象。

ラムダ本体を、
引数型 A を追加した環境で
型付けする。

推論規則

    A :: Γ ⊢ t : B
    --------------------
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
Function application.

Inference rule

    Γ ⊢ t : A ⇒ B
    Γ ⊢ u : A
    ----------------
      Γ ⊢ t u : B
-/

/-
関数適用。

関数の型と
引数の型が一致すれば、

結果は返り値の型になる。

推論規則

    Γ ⊢ t : A ⇒ B
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

という数学的な記法で
書けるようにする。
-/
notation:50 Γ " ⊢ " t " : " A =>
  HasType Γ t A

theorem lookup_nil
    {x : Index}
    {A : Ty} :
    ¬ Lookup [] x A := by
  intro h
  cases h

------------------------------------------------------------
-- Examples
------------------------------------------------------------

/--
The identity function.

The term

    λx.x

has type

    base ⇒ base.
-/

/-
恒等関数。

λx.x は

base ⇒ base

型を持つ。
-/
example :
    [] ⊢ (ƛ #0) : (Ty.base ⇒ Ty.base) := by
  apply HasType.lam
  apply HasType.var
  exact Lookup.here

end STLC