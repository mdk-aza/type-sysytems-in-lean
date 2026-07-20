import Mathlib.Data.String.Basic
import TypeSystemsInLean.PLFABased.Syntax

namespace STLC

open Term

------------------------------------------------------------
-- Renaming
------------------------------------------------------------

/--
Renaming for de Bruijn indices.

A renaming changes de Bruijn indices while preserving
the binding structure of a term.

Renaming is simpler than substitution and serves as the
foundation for implementing substitution.

The definitions in this file are used later in

    Substitution
        ↓
    Substitution Lemma
        ↓
    Preservation
        ↓
    Soundness
-/

/-
de Bruijn index に対するリネーム (renaming)。

リネームは、束縛構造を保ったまま
de Bruijn index の番号だけを付け替える操作である。

de Bruijn index では、ラムダ抽象へ入るたびに
各変数番号の意味が変化する。

そのため、変数番号を書き換える操作を
独立した概念として定義する。

リネームは置換 (substitution) よりも単純であり、
置換を実装するための土台となる。

このファイルで定義する内容は

    Substitution
        ↓
    置換補題 (Substitution Lemma)
        ↓
    型保存性 (Preservation)
        ↓
    型安全性 (Soundness)

へと利用される。

特に `shift` は、
ラムダ抽象へ入る際に自由変数番号を1つ増やし、
変数捕獲 (variable capture) を防ぐための基本操作である。
-/

/-
A renaming maps each de Bruijn index to another index.
-/

/-
リネームを表す。

`ρ : Index → Index` は、
各 de Bruijn index をどの番号へ付け替えるかを表す写像である。

例:

ρ 0 = 2
ρ 1 = 5
ρ 2 = 1

なら

#0 ↦ #2
#1 ↦ #5
#2 ↦ #1

という番号の付け替えを表す。
-/
abbrev Renaming := Index → Index

------------------------------------------------------------
-- Identity renaming
------------------------------------------------------------

/--
Identity renaming.
-/

/-
恒等リネーム。

すべての変数番号をそのまま保つ。

    #0 ↦ #0
    #1 ↦ #1
    #2 ↦ #2

となる。
-/
def ids : Renaming :=
  fun x => x

------------------------------------------------------------
-- Shift
------------------------------------------------------------

/--
Shift every free variable by one.
-/

/-
シフト。

すべての自由変数番号を1だけ増やす。

    #0 ↦ #1
    #1 ↦ #2
    #2 ↦ #3

ラムダ抽象へ入るとき、
新しく #0 が束縛変数として導入される。

そのため自由変数との衝突
（variable capture）を防ぐ目的で利用される。
-/
def shift : Renaming :=
  fun x => x + 1

------------------------------------------------------------
-- Extension
------------------------------------------------------------

/--
Extend a renaming under a lambda abstraction.

The newly bound variable (`#0`) is left unchanged,
while the remaining variables are renamed under the
new binder.
-/

/-
ラムダ抽象の内部でリネームを1段拡張する。

新しく束縛された変数

    #0

はそのまま残す。

それ以外は

    n + 1 ↦ ρ n + 1

とする。

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

となるため、
リネームも1段拡張する必要がある。
-/
def ext (ρ : Renaming) : Renaming
| 0     => 0
| n + 1 => ρ n + 1

------------------------------------------------------------
-- Composition
------------------------------------------------------------

/--
Composition of renamings.

Corresponds to function composition used throughout the
PLFA DeBruijn and Substitution chapters.
-/

/-
リネームの合成。

まず `ρ₁` を適用し、
その後 `ρ₂` を適用する。

【PLFA対応】

PLFA DeBruijn 章および Substitution 章で
用いられるリネームの合成（関数合成）に対応する。

Lean では可読性を高めるため、
専用の演算子 `∘r` として定義する。
-/
def compose (ρ₂ ρ₁ : Renaming) : Renaming :=
  fun x => ρ₂ (ρ₁ x)

infixr:90 " ∘r " => compose

------------------------------------------------------------
-- Renaming
------------------------------------------------------------

/--
Apply a renaming to every free variable in a term.

Variables are renamed according to `ρ`.

When entering a lambda abstraction,
the renaming is extended using `ext`
so that the newly bound variable (`#0`)
remains bound.

This definition forms the basis of
substitution and its metatheory.
-/

/-
項全体にリネームを適用する。

自由変数はリネーム写像 `ρ`
に従って番号を付け替える。

ラムダ抽象へ入ると、
新しい束縛変数 `#0` が導入されるため、
`ext` によりリネームを1段拡張して再帰する。

この定義は

    rename-id
    compose-rename
        ↓
    substitution
        ↓
    Substitution Lemma
        ↓
    Preservation

の基礎となる。
-/
def rename (ρ : Renaming) : Term → Term
| .var x =>
    -- Rename a variable.
    -- 変数番号を付け替える。
    .var (ρ x)

| .lam t =>
    -- Enter a binder.
    -- Extend the renaming before recurring.
    -- Extend a renaming underneath a binder.
    --
    -- ラムダ抽象へ入るので
    -- リネームを1段拡張する。
    -- binder の下へ降りる
    .lam (rename (ext ρ) t)

| .ap t u =>
    -- Rename both subterms independently.
    --
    -- 関数適用では左右の部分項へ
    -- 独立にリネームを適用する。
    .ap (rename ρ t)
        (rename ρ u)

------------------------------------------------------------
-- Notation
------------------------------------------------------------

/--
Notation for applying a renaming.
-/

/-
リネーム適用の記法。

    t⟪ρ⟫

は

    rename ρ t

を表す。

数学では

    ρ(t)

などと書かれることもあるが、

Lean では置換

    t⟦σ⟧

と区別するため

    t⟪ρ⟫

という記法を採用している。
-/
notation t "⟪" ρ "⟫" => rename ρ t

------------------------------------------------------------
-- Renaming lemmas
------------------------------------------------------------

/--
The extension of the identity renaming is the identity renaming.

Lean helper lemma.

This lemma simplifies proofs involving `rename`.
-/

/-
恒等リネームを拡張しても、
再び恒等リネームになる。

【Lean実装用の補助補題】

ラムダ抽象の内部へ入っても、
恒等リネームは何も変更しないことを表す。

PLFA では計算規則として暗黙に扱われることが多いが、
Lean では書き換え (`rw`) を容易にするため
明示的に補題として証明している。
-/
theorem ext_ids :
    ext ids = ids := by
  -- 関数の外延性 (Function Extensionality)
  funext x
  cases x with
  | zero =>
      rfl
  | succ n =>
      rfl

/--
Applying the identity renaming leaves a term unchanged.

Corresponds to `rename-id` in the PLFA Substitution chapter.
-/

/-
恒等リネームを適用しても、
項は変化しない。

【PLFA対応】

PLFA Substitution 章の

    rename-id

に対応する補題である。

これは

「rename が本当に何も変更しない場合」

を保証する最も基本的な性質であり、
後続のリネーム・置換に関する補題の出発点となる。
-/
theorem rename_ids :
    ∀ t : Term, t⟪ids⟫ = t := by
  intro t
  induction t with
  | var x =>
      rfl

  | lam t ih =>
      simp [rename]
      rw [ext_ids]
      exact ih

  | ap t u iht ihu =>
      simp [rename, iht, ihu]

/--
Shifting commutes with extending a renaming.

Applying a renaming and then shifting is equivalent to
first shifting and then applying the extended renaming.
-/

/-
シフトとリネームの拡張は可換である。

変数番号を書き換えてからシフトすることは、

先にシフトしてから
拡張されたリネームを適用することと等しい。

【Lean実装用の補助補題】

この補題は

* rename-subst
* subst-comp

などのラムダ抽象ケースで繰り返し利用される。

PLFA では計算規則として自然に現れる性質であるが、
Lean では書き換えを容易にするため
補題として独立に証明している。
-/
theorem shift_ext
    (ρ : Renaming) :
    shift ∘r ρ =
    ext ρ ∘r shift := by
  funext x
  rfl

/--
Extension preserves composition of renamings.

Extending a composed renaming is equivalent to composing
the extended renamings.

Lean helper lemma.
-/

/-
リネームの合成を拡張しても、

それぞれを拡張してから合成することと等しい。

つまり

    ext (ρ₂ ∘r ρ₁)

と

    ext ρ₂ ∘r ext ρ₁

は同じリネームになる。

【Lean実装用の補助補題】

PLFA の compose-ext に対応する考え方である。

Lean では
ラムダ抽象ケースでの書き換えを簡潔にするため、
この形で補題として証明している。
-/
theorem ext_comp
    (ρ₁ ρ₂ : Renaming) :
    ext (ρ₂ ∘r ρ₁)
      =
    (ext ρ₂) ∘r (ext ρ₁) := by
  funext x
  cases x with
  | zero =>
      rfl
  | succ n =>
      rfl

/--
Composing two renamings is equivalent to applying
their composition once.

Corresponds to `compose-rename`
in the PLFA Substitution chapter.
-/

/-
リネームを2回適用することは、

合成したリネームを
1回だけ適用することと等しい。

つまり

    rename ρ₂ (rename ρ₁ t)

は

    rename (ρ₂ ∘r ρ₁) t

と一致する。

【PLFA対応】

PLFA Substitution 章の

    compose-rename

に対応する補題である。

この補題は

* rename-subst
* subst-comp

などの基礎となり、

最終的には

    Substitution Lemma
        ↓
    Preservation
        ↓
    Soundness

へと利用される重要な基本補題である。
-/
theorem rename_comp :
    ∀ t,
    ∀ ρ₁ ρ₂,
      (t⟪ρ₁⟫)⟪ρ₂⟫ =
      t⟪ρ₂ ∘r ρ₁⟫ := by
  intro t
  induction t with
  | var x =>
      intro ρ₁ ρ₂
      rfl

  | lam t ih =>
      intro ρ₁ ρ₂
      simp [rename]
      rw [ext_comp]
      exact ih (ext ρ₁) (ext ρ₂)

  | ap t u iht ihu =>
      simp [rename, iht, ihu]

end STLC