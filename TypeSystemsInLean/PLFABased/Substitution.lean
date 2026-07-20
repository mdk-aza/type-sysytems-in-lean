import TypeSystemsInLean.PLFABased.Syntax
import TypeSystemsInLean.PLFABased.Rename

namespace STLC

open Term

------------------------------------------------------------
-- Substitution
------------------------------------------------------------

/--
Substitution for de Bruijn indices.

A substitution maps each de Bruijn index to a term.

Substitution is the core operation used for

    β-reduction
        ↓
    Substitution Lemma
        ↓
    Preservation

When entering a lambda abstraction, the substitution must be
extended to avoid variable capture.
-/

/-
de Bruijn index に対する置換 (substitution)。

置換は

    β簡約
        ↓
    置換補題 (Substitution Lemma)
        ↓
    型保存性 (Preservation)

の基礎となる最も重要な操作である。

ラムダ抽象の内部へ入るときは、
変数捕獲 (variable capture) を防ぐため、
置換を拡張する必要がある。
-/

/-
A substitution maps each de Bruijn index to a term.
-/

/-
置換を表す。

`σ : Index → Term` は、
各 de Bruijn index をどの項へ置き換えるかを表す写像である。

例:

σ 0 = #2
σ 1 = ƛ #0
σ 2 = #5

であれば

#0 ↦ #2
#1 ↦ λ.#0
#2 ↦ #5

という置換を表す。
-/
abbrev Subst := Index → Term

/--
Extend a substitution under a lambda abstraction.

The newly bound variable (`#0`) is left unchanged.

All remaining substituted terms are shifted so that
free variables are not captured by the new binder.
-/

/-
ラムダ抽象の内部で置換を1段拡張する。

新しく束縛された変数 `#0` は
そのラムダ自身が束縛する変数なので置換しない。

それ以外の置換結果については
`shift` を適用して自由変数番号を1つ増やし、
新しい束縛変数による
変数捕獲 (variable capture) を防ぐ。

概念的には

    λ の外

        #2
        #1
        #0

           ↓ λ に入る

        #3
        #2
        #1
        #0   ← 新しい束縛変数

したがって

    exts σ

    0     ↦ #0
    n + 1 ↦ shift (σ n)
-/
def exts (σ : Subst) : Subst
| 0     => #0
| n + 1 => (σ n)⟪shift⟫

/--
Apply a substitution to a term.

Variables are replaced according to the substitution.

When entering a lambda abstraction,
the substitution is extended using `exts`
so that bound variables remain bound.

This definition is the basis of β-reduction and
the Substitution Lemma.
-/

/-
項全体へ置換を適用する。

変数は置換写像 `σ` に従って置き換える。

ラムダ抽象へ入ると、
新しい束縛変数 `#0` が導入されるため、
`exts` によって置換を拡張して再帰する。

もし `exts` を使わず

    subst σ t

としてしまうと、

置換後の自由変数が
新しいラムダに束縛されてしまう
(variable capture)。

そのため `shift` を含む `exts`
が必要になる。

この定義は

    β簡約
        ↓
    置換補題
        ↓
    型保存性

の土台となる。
-/
def subst (σ : Subst) : Term → Term
| .var x =>
    -- Replace a variable.
    -- 変数は置換写像に従って置き換える。
    σ x

| .lam t =>
    -- Enter a binder.
    -- Extend the substitution before recurring.
    --
    -- ラムダ抽象へ入るので
    -- exts によって置換を拡張する。
    .lam (subst (exts σ) t)

| .ap t u =>
    -- Apply substitution independently to both subterms.
    --
    -- 関数適用では左右の部分項へ
    -- 独立に置換を適用する。
    .ap (subst σ t)
        (subst σ u)

/--
Apply a renaming to every term produced by a substitution.

This is the action of a renaming on substitutions.
-/

/-
置換が生成する各項へリネームを適用する。

つまり

    σ

    0 ↦ t₀
    1 ↦ t₁
    2 ↦ t₂

なら

    mapSubst ρ σ

    0 ↦ rename ρ t₀
    1 ↦ rename ρ t₁
    2 ↦ rename ρ t₂

となる。

Lean 実装では

* rename-subst
* subst-comp

などの補題を自然に記述するための
補助定義として用いる。
-/
def mapSubst (ρ : Renaming) (σ : Subst) : Subst :=
  fun x => (σ x)⟪ρ⟫

------------------------------------------------------------
-- Single substitution
------------------------------------------------------------

/--
Substitute a term for variable `#0`.

Variables above `#0` are decremented because
one binder disappears after β-reduction.
-/

/-
変数 `#0` を1つの項で置き換える置換。

β簡約

    (ƛ t) □ v

を

    t[v/#0]

へ変換するときに用いる。

ラムダが1つ取り除かれるため、
残りの変数番号は1だけ小さくなる。

対応は

    0 ↦ v
    1 ↦ #0
    2 ↦ #1
    3 ↦ #2

となる。
-/
def single (v : Term) : Subst
| 0     => v
| n + 1 => #n

------------------------------------------------------------
-- Notation
------------------------------------------------------------

/--
Notation for applying a substitution.
-/

/-
置換適用の記法。

    t⟦σ⟧

は

    subst σ t

を表す。

数学では

    t[σ]

と書くことが多いが、

Lean では rename と区別しやすくするため

    t⟦σ⟧

という記法を採用している。

β簡約では

    (ƛ t) □ v

を

    t⟦single v⟧

へ変換する。
-/
notation t "⟦" σ "⟧" => subst σ t

end STLC