import TypeSystemsInLean.PLFABasedSTLC.Substitution
import TypeSystemsInLean.PLFABasedSTLC.TypingLemmas
/-!
# Substitution Lemma

This file proves the substitution lemma for the
Simply Typed Lambda Calculus (STLC).

The substitution lemma states that replacing variables
with well-typed terms preserves typing.

It is one of the central metatheorems of STLC and forms
the foundation of the proofs of

* Preservation
* Soundness

This corresponds to the substitution lemma
in the PLFA Lambda chapter.
-/

/-!
# 置換補題

このファイルでは
Simply Typed Lambda Calculus (STLC)
の置換補題を証明する。

置換補題とは

「型付けされた項で変数を置き換えても、
項全体の型は保存される」

という性質である。

これは

* Preservation
* Soundness

を証明するための最重要補題であり、

PLFA Lambda 章の
Substitution Lemma に対応する。
-/

namespace STLC

/--
A substitution that preserves typing.

A typed substitution maps every well-typed variable
in one context to a well-typed term
of the same type in another context.

This is the substitution analogue of
`TypedRenaming`.
-/

/-
型付き置換。

型付き置換とは、

型環境 Γ において
型付けされた各変数を、

型環境 Δ において
同じ型を持つ項へ置き換える置換である。

これは
`TypedRenaming`
の置換版である。
-/
abbrev TypedSubstitution
    (Γ Δ : Context)
    (σ : Subst) : Prop :=
  ∀ {x A},
    Lookup Γ x A →
    HasType Δ (σ x) A


/--
Extend a typed substitution underneath a binder.

When entering a lambda abstraction,
the newly bound variable is mapped to itself,
while the remaining substitution is shifted.

The extended substitution continues to preserve typing.
-/

/-
型付き置換の拡張。

ラムダ抽象の内部へ入ると、

新しく束縛された変数は
そのまま変数 #0 に対応し、

それ以外の置換対象は
1段シフトされる。

拡張後も
型付き置換の性質は保存される。
-/
theorem extTypedSubstitution
    {Γ Δ : Context}
    {σ : Subst}
    {A : Ty}
    (hσ : TypedSubstitution Γ Δ σ) :
    TypedSubstitution
      (A :: Γ)
      (A :: Δ)
      (exts σ) := by
  intro x T h
  cases h with
  | here =>
      simp [exts]
      exact HasType.var Lookup.here

  | there h =>
      simp [exts]
      exact shift_preserves (hσ h)



/--
Typed substitutions preserve variable lookup.
-/

/-
型付き置換は
変数参照を保存する。

変数参照に対応する項を
置換から取り出すことで、

同じ型を持つ項が得られる。

置換補題の変数ケースに対応する。
-/
theorem subst_lookup
    {Γ Δ : Context}
    {σ : Subst}
    (hσ : TypedSubstitution Γ Δ σ)
    {x : Index}
    {A : Ty}
    (h : Lookup Γ x A) :
    HasType Δ (σ x) A := by
  exact hσ h



/--
Substitution preserves typing.

Applying a typed substitution to a well-typed term
produces another well-typed term of the same type.

Corresponds to the substitution lemma in PLFA.
-/

/-
置換は型付けを保存する。

型付き置換を項全体へ適用しても、
項の型は保存される。

PLFA の Substitution Lemma に対応する。
-/
theorem subst_preserves
    {Γ Δ : Context}
    {σ : Subst}
    (hσ : TypedSubstitution Γ Δ σ)
    {t : Term}
    {A : Ty}
    (ht : HasType Γ t A) :
    HasType Δ (t⟦σ⟧) A := by
  induction ht generalizing Δ σ with
  | var h =>
      simp [subst]
      exact subst_lookup hσ h

  | lam ht ih =>
      simp [subst]
      apply HasType.lam
      apply ih
      exact extTypedSubstitution hσ

  | ap ht₁ ht₂ ih₁ ih₂ =>
      simp [subst]
      exact HasType.ap
        (ih₁ hσ)
        (ih₂ hσ)
  end STLC