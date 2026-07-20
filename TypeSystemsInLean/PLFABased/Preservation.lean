import TypeSystemsInLean.PLFABased.Typing
import TypeSystemsInLean.PLFABased.SubstitutionLemma
import TypeSystemsInLean.PLFABased.Evaluation

/-!
# Preservation

If a well-typed term takes one evaluation step,
its type is preserved.

This is one half of the type safety theorem.
-/

/-!
# Preservation（型保存）

型付き項が1ステップ評価されても，
その型は変化しないことを示す。

これは型安全性（Type Safety）の半分を構成する。
-/

namespace STLC

/--
Preservation theorem.

If

    Γ ⊢ t : A

and

    t ⟶ t'

then

    Γ ⊢ t' : A.
-/

/-
型保存定理。

Γ ⊢ t : A
かつ
t ⟶ t'

ならば

Γ ⊢ t' : A
である。
-/
theorem preservation
    {Γ : Context}
    {t t' : Term}
    {A : Ty}
    (ht : HasType Γ t A)
    (hs : t ⟶ t') :
    HasType Γ t' A := by

  induction hs generalizing Γ A with

  ----------------------------------------------------------------
  -- β
  ----------------------------------------------------------------

  | beta hv =>
      cases ht with
      | ap hLam hArg =>
          cases hLam with
          | lam hBody =>
              simpa using
                subst_preserves
                  (Γ := _ :: Γ)
                  (Δ := Γ)
                  (σ := single _)
                  (hσ := by
                    intro x T h
                    cases h with
                    | here =>
                        simpa [single]
                          using hArg
                    | there h =>
                        exact HasType.var h)
                  hBody

  ----------------------------------------------------------------
  -- app₁
  ----------------------------------------------------------------

  | app₁ hs ih =>
      cases ht with
      | ap h₁ h₂ =>
          exact HasType.ap
            (ih h₁)
            h₂

  ----------------------------------------------------------------
  -- app₂
  ----------------------------------------------------------------

  | app₂ hv hs ih =>
      cases ht with
      | ap h₁ h₂ =>
          exact HasType.ap
            h₁
            (ih h₂)

end STLC