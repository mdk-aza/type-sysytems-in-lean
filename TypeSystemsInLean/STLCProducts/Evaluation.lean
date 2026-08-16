import TypeSystemsInLean.STLCProducts.Syntax
import TypeSystemsInLean.STLCProducts.Substitution

/-!
# Evaluation

This file defines the small-step operational semantics
of the Simply Typed Lambda Calculus (STLC).

Evaluation is defined by a one-step reduction relation.

This corresponds to the reduction rules
in the PLFA Lambda chapter.
-/

/-!
# 評価

このファイルでは
Simply Typed Lambda Calculus (STLC)
の小ステップ評価（small-step semantics）
を定義する。

評価とは

    「プログラムを1ステップだけ実行する」

関係である。

PLFA の Lambda 章における
評価規則に対応する。
-/

namespace STLC

open Term

------------------------------------------------------------
-- Values
------------------------------------------------------------

/--
Values.

A value is a fully evaluated term.

In STLC,
only lambda abstractions are values.
-/

/-
値。

値とは

「これ以上評価する必要のない項」

である。

STLC では

ラムダ抽象だけが値となる。

推論規則：

    --------------
      Value (λ t)
-/
inductive Value : Term → Prop where
| lam :
    ∀ t,
    Value (ƛ t)
/--
A pair is a value when both components are values.

推論規則：

Value v₁    Value v₂
--------------------
Value (v₁, v₂)
-/
| pair :
    ∀ v₁ v₂,
    Value v₁ →
    Value v₂ →
    Value (v₁, v₂)


------------------------------------------------------------
-- Small-step Evaluation
------------------------------------------------------------

/--
One-step reduction.

    t ⟶ t'

means that

t evaluates to t'
in one computation step.
-/

/-
1ステップ評価。

    t ⟶ t'

とは

「項 t が1回の評価で
t' に変化する」

ことを表す。

評価戦略は
Call-by-Value とする。
-/
inductive Step : Term → Term → Prop where

/--
β-reduction.
-/

/-
β簡約。

関数部分がラムダ抽象であり、
引数が値であれば、

ラムダ本体へ
引数を代入する。

推論規則：

      Value v
--------------------------
(λ t) v ⟶ t[v]
-/
| beta
    {t v}
    :
    Value v →
    Step
      ((ƛ t) □ v)
      (t⟦single v⟧)

/--
Evaluate the function position.
-/

/-
関数側の評価。

関数部分がまだ評価できるなら、
先に関数を評価する。

推論規則：

 t₁ ⟶ t₁'
-------------------
t₁ t₂ ⟶ t₁' t₂
-/
| app₁
    {t₁ t₁' t₂}
    :
    Step t₁ t₁' →
    Step
      (t₁ □ t₂)
      (t₁' □ t₂)

/--
Evaluate the argument.
-/

/-
引数側の評価。

関数が値であり、

引数がまだ評価できるなら、
引数を評価する。

推論規則：

 Value v
 t₂ ⟶ t₂'
--------------------
v t₂ ⟶ v t₂'
-/
| app₂
    {v t₂ t₂'}
    :
    Value v →
    Step t₂ t₂' →
    Step
      (v □ t₂)
      (v □ t₂')

| pair₁
    {t₁ t₁' t₂ : Term}
    :
    Step t₁ t₁' →
    Step (t₁, t₂) (t₁', t₂)

| pair₂
    {v₁ t₂ t₂' : Term}
    :
    Value v₁ →
    Step t₂ t₂' →
    Step (v₁, t₂) (v₁, t₂')

| proj1₁
    {t t'}
    :
    Step t t' →
    Step (proj1 t) (proj1 t')

| proj1Pair
    {v₁ v₂}
    :
    Value v₁ →
    Value v₂ →
    Step (proj1 (v₁, v₂)) v₁

| proj2₁
    {t t'}
    :
    Step t t' →
    Step (proj2 t) (proj2 t')

| proj2Pair
    {v₁ v₂}
    :
    Value v₁ →
    Value v₂ →
    Step (proj2 (v₁, v₂)) v₂


------------------------------------------------------------
-- Notation
------------------------------------------------------------

/--
Reduction notation.
-/

/-
評価関係の記法。

    t ⟶ t'

と書けるようにする。
-/
infix:40 " ⟶ " => Step

@[simp]
theorem value_not_step
    {v t}
    (hv : Value v) :
    ¬ Step v t := by
  intro hs
  cases hv with
  | lam =>
      cases hs
  | pair v₁ v₂ hv₁ hv₂ =>
      cases hs
      · exact value_not_step hv₁ ‹_›
      · exact value_not_step hv₂ ‹_›
------------------------------------------------------------
-- Examples
------------------------------------------------------------

/--
Identity function reduces in one β-step.
-/

/-
恒等関数の適用は
1ステップで簡約される。
-/
example :
    ((ƛ #0) □ (ƛ #0))
      ⟶
    (ƛ #0) := by
  apply Step.beta
  exact Value.lam _

end STLC