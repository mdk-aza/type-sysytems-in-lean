import TypeSystemsInLean.PLFABased.Typing
import TypeSystemsInLean.PLFABased.Rename

namespace STLC


/--
Weakening for variable lookup.

If a variable has type `A` in a typing context `Γ`,
then the same variable is still well-typed after extending
the context with a new binding.

This corresponds to the weakening property for variables.
-/

/-
変数参照に対する Weakening。

型環境 Γ の中で型 A を持つ変数は、

新しい束縛を追加した環境

    B :: Γ

でも同じ型 A を持つ。

PLFA における
変数参照の Weakening に対応する基本補題である。
-/
theorem lookup_weaken
     {Γ : Context}
     {x : Index}
     {A B : Ty}
     (h : Lookup Γ x A) :
     Lookup (B :: Γ) (x + 1) A := by
   exact Lookup.there h

/--
A renaming that preserves typing.

A typed renaming maps every well-typed variable
in one context to a variable of the same type
in another context.

Unlike ordinary renamings (`Index → Index`),
this relation records that typing information
is preserved.
-/

/-
型付きリネーム。

通常のリネームは

    Index → Index

で表されるが、

型付きリネームは

「型環境 Γ で型付けされた変数を、
型環境 Δ において同じ型の変数へ写す」

ことを保証する。

Typing の補題では、
この性質を仮定して証明を行う。
-/
def TypedRenaming
    (Γ Δ : Context)
    (ρ : Renaming) : Prop :=
  ∀ {x A},
    Lookup Γ x A →
    Lookup Δ (ρ x) A

/--
Extending a typed renaming underneath a binder.

When entering a lambda abstraction,
both typing contexts gain the same bound variable.

The extended renaming continues to preserve typing.
-/

/-
型付きリネームの拡張。

ラムダ抽象の内部へ入ると、

両方の型環境に
同じ束縛変数が追加される。

そのため、
リネームも `ext` によって拡張すると、
引き続き型を保存する。

PLFA における binder の下への
リネーム拡張に対応する。
-/
theorem extTypedRenaming
    {Γ Δ : Context}
    {ρ : Renaming}
    {A : Ty}
    (hρ : TypedRenaming Γ Δ ρ) :
    TypedRenaming (A :: Γ) (A :: Δ) (ext ρ) := by
  intro x T h
  cases h with
  | here =>
      exact Lookup.here
  | there h =>
      exact Lookup.there (hρ h)

/--
Typed renamings preserve variable lookup.

If a variable lookup is valid in `Γ`,
then after applying a typed renaming,
the corresponding lookup is valid in `Δ`.
-/

/-
型付きリネームは
変数参照を保存する。

Γ で正しく型付けされた変数は、

型付きリネームによって対応する変数へ写されても、

Δ で同じ型を持つ。

これは rename_preserves の
変数ケースで利用される基本補題である。
-/
theorem rename_lookup
    {Γ Δ : Context}
    {ρ : Renaming}
    (hρ : TypedRenaming Γ Δ ρ)
    {x : Index}
    {A : Ty}
    (h : Lookup Γ x A) :
    Lookup Δ (ρ x) A := by
  exact hρ h

/--
Renaming preserves typing.

Applying a typed renaming to a well-typed term
produces another well-typed term
with the same type.

This is one of the central metatheorems
for the Simply Typed Lambda Calculus.

Corresponds to the renaming lemma in PLFA.
-/

/-
リネームは型付けを保存する。

型付きリネームを
項全体へ適用しても、

項の型は変化しない。

これは STLC における
最も重要な基本補題の一つであり、

後続の

* Substitution Lemma
* Preservation
* Soundness

の証明の土台となる。

PLFA の Renaming Lemma に対応する。
-/
theorem rename_preserves
    {Γ Δ : Context}
    {ρ : Renaming}
    (hρ : TypedRenaming Γ Δ ρ)
    {t : Term}
    {A : Ty}
    (ht : HasType Γ t A) :
    HasType Δ (t⟪ρ⟫) A := by
  induction ht generalizing Δ ρ with
  | var h =>
      -- Variables are renamed using the typed renaming.
      --
      -- 型付きリネームにより
      -- 変数参照は保存される。
      simp [rename]
      exact HasType.var (rename_lookup hρ h)

  | lam ht ih =>
      -- Under a binder, extend the renaming.
      --
      -- ラムダ抽象の内部では
      -- リネームを ext で拡張する。
      simp [rename]
      apply HasType.lam
      apply ih
      exact extTypedRenaming hρ

  | ap ht₁ ht₂ ih₁ ih₂ =>
      -- Rename both subterms independently.
      --
      -- 関数適用では
      -- 左右の部分項へ独立にリネームを適用する。
      simp [rename]
      exact HasType.ap
        (ih₁ hρ)
        (ih₂ hρ)


/--
Shifting preserves typing.

Weakening a typing context and shifting every free variable
preserves typing.
-/

/-
shift は型付けを保存する。

型環境へ新しい束縛を追加し、
自由変数を1つシフトしても
型付けは保存される。

これは extTypedSubstitution の証明で利用する。
-/
theorem shift_preserves
    {Γ : Context}
    {t : Term}
    {A B : Ty}
    (ht : HasType Γ t A) :
    HasType (B :: Γ) (t⟪shift⟫) A := by
  apply rename_preserves
  · intro x T h
    exact lookup_weaken h
  · exact ht

end STLC
