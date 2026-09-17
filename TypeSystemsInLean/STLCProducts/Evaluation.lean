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

-- valueの扱い
-- λ計算の場合
-- 単独の場合、CVVは変数自体もValue
-- プログラミング言語の場合
-- 変数単独で評価する場合
inductive Value : Term → Prop where
  | lam :
    ∀ t,
    Value (ƛ t)
    /--
    A pair is a value when both components are values.

    推論規則：

    Value v₁ Value v₂
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

-- 場合によっては、関数でかける Termを受け取って、Boolで返す
-- 1ステップ計算が関数にできない、想定しているものが来ないため。部分関数でもかける。Lean
-- Ocamlなどではタグ付けなどして、NaNを返すなどがある。
-- 関数をかけるなら、それが一番楽。Evaluatorはたいていは関数ではかけない。


-- 2引数の述語をSTEPという名前で帰納的に定義
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
  -- 命題論理→述語論理→帰納定義
  -- t = 0 + 1 * 2
  -- v = \x.x
  -- t [[ single v ]] = ?

-- t = pair(0, 1) //Term pair
-- t [[ single v ]] = subst (single v) t
-- = pair(subst (single v) (var 0))(subst (single v) (var 1))
-- = pair((single v) 0 , (single v) 1 )
-- = pair(\x.x, 0)
--  0 @ 1 @ 2 @ 3[[single v]]
--  @ 0 @ 1 @ 2


-- def single (v : Term) : Subst
-- | 0     => v
-- | n + 1 => #n

-- def subst (σ : Subst) : Term → Term
-- | .var x =>
--      σ x
-- | .pair t1 t2 =>
    -- .pair (subst σ t1)
          -- (subst σ t2)

-- t = single v
-- v = \x.x


-- notation t "⟦" σ "⟧" => subst σ t

-- abbrev Subst := Index → Term
-- def subst (σ : Subst) : Term → Term


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

-- end of inductive Step

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


end STLC