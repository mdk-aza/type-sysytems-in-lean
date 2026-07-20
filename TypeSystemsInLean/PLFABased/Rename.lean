import Mathlib.Data.String.Basic
import TypeSystemsInLean.PLFABased.Syntax

namespace STLC

open Term

------------------------------------------------------------
-- Renaming
------------------------------------------------------------

abbrev Renaming := Index → Index

------------------------------------------------------------
-- Identity renaming
------------------------------------------------------------

def ids : Renaming :=
  fun x => x

------------------------------------------------------------
-- Shift
------------------------------------------------------------

def shift : Renaming :=
  fun x => x + 1

------------------------------------------------------------
-- Extension
------------------------------------------------------------

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

まず ρ₁ を適用し、
その後に ρ₂ を適用する。

【PLFA対応】

PLFA DeBruijn 章および Substitution 章で
用いられるリネームの合成（関数合成）に対応する。
Leanでは可読性を高めるため、
専用の演算子 `∘r` として定義する。
-/
def comp (ρ₂ ρ₁ : Renaming) : Renaming :=
  fun x => ρ₂ (ρ₁ x)

infixr:90 " ∘r " => comp

------------------------------------------------------------
-- Renaming
------------------------------------------------------------
/--
Apply a renaming to all free variables in a term.

A renaming `ρ : Index → Index` specifies how de Bruijn indices
are transformed.

When entering a lambda abstraction, the renaming is extended
using `ext` so that the newly bound variable (`#0`) remains bound.
This definition serves as the basis for substitution and its
associated metatheory.
-/

/-
項中の自由変数に対してリネーム（変数番号の付け替え）を行う。

`ρ : Index → Index` は各 de Bruijn index をどのように
変換するかを表す。

ラムダ抽象の内部では、新しく束縛された変数 `#0` を
そのまま束縛変数として扱うため、`ext` によりリネームを
拡張して再帰的に適用する。

この定義は、置換 (substitution) およびその後の
メタ理論（置換補題、型保存性など）の基礎となる。
-/

def rename (ρ : Renaming) : Term → Term
| .var x =>
    .var (ρ x)

| .lam t =>
    .lam (rename (ext ρ) t)

| .ap t u =>
    .ap (rename ρ t)
        (rename ρ u)

------------------------------------------------------------
-- Notation
------------------------------------------------------------

notation t "⟪" ρ "⟫" => rename ρ t

------------------------------------------------------------
-- Renaming lemmas
------------------------------------------------------------

/--
The extension of the identity renaming is the identity renaming.

Lean helper lemma.

This lemma is introduced for the Lean implementation to simplify
proofs involving `rename`. It does not appear explicitly in PLFA,
where the corresponding equality is usually handled implicitly.
-/

/-
恒等リネームを拡張しても、
再び恒等リネームになる。

【Lean実装用の補助補題】

この補題は Lean で `rename` の証明を簡潔にするために導入した。
PLFA には同名の補題は登場しないが、
同等の性質は証明中で暗黙に利用されている。
-/
theorem ext_ids :
    ext ids = ids := by
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
`rename-id`
に対応する補題。
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

This lemma states that applying a renaming and then shifting
is equivalent to first shifting and then applying the extended
renaming.

It is used to relate renaming and substitution under
lambda abstractions.
-/

/-
シフトとリネームの拡張は可換である。

変数をリネームしてからシフトすることは、
先にシフトしてから拡張されたリネームを適用することと等しい。

【Lean実装用の補助補題】

`rename-subst` や `subst-comp` の
ラムダ抽象ケースで繰り返し利用される基本補題である。

PLFA ではこの等式は計算規則として暗黙に扱われることが多いが、
Lean では明示的な補題として証明しておくことで、
書き換え (`rw`) による証明が簡潔になる。
-/
theorem shift_ext
    (ρ : Renaming) :
    shift ∘r ρ =
    ext ρ ∘r shift := by
  funext x
  rfl

/--
Extension preserves composition of renamings.

Lean helper lemma.

This lemma corresponds to the idea behind `compose-ext` in PLFA,
but is stated in a form that is more convenient for Lean proofs.
-/

/-
リネームの合成を拡張しても、
それぞれを拡張してから合成するのと同じになる。

【Lean実装用の補助補題】

PLFA の compose-ext に対応する考え方であるが、
Lean では書き換えを容易にするため
この形で証明している。
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
合成したリネームを1回適用することと等しい。

【PLFA対応】

PLFA Substitution 章の
`compose-rename`
に対応する補題。
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