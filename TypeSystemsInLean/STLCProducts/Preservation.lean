import TypeSystemsInLean.STLCProducts.Typing
import TypeSystemsInLean.STLCProducts.SubstitutionLemma
import TypeSystemsInLean.STLCProducts.Evaluation

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

  -- β
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
                        simpa [single] using hArg
                    | there h =>
                        exact HasType.var h)
                  hBody

  -- app₁
  | app₁ hs ih =>
      cases ht with
      | ap h₁ h₂ =>
          exact HasType.ap
            (ih h₁)
            h₂

  -- app₂
  | app₂ hv hs ih =>
      cases ht with
      | ap h₁ h₂ =>
          exact HasType.ap
            h₁
            (ih h₂)

  -- pair₁
  | pair₁ hs ih =>
      cases ht with
      | pair h₁ h₂ =>
          exact HasType.pair
            (ih h₁)
            h₂

  -- pair₂
  | pair₂ hv hs ih =>
      cases ht with
      | pair h₁ h₂ =>
          exact HasType.pair
            h₁
            (ih h₂)

  -- proj1₁
  | proj1₁ hs ih =>
      cases ht with
      | proj1Ty h =>
          exact HasType.proj1Ty
            (ih h)

  -- proj1Pair
  | proj1Pair hv₁ hv₂ =>
      cases ht with
      | proj1Ty h =>
          cases h with
          | pair h₁ h₂ =>
              exact h₁

  -- proj2₁
  | proj2₁ hs ih =>
      cases ht with
      | proj2Ty h =>
          exact HasType.proj2Ty
            (ih h)

  -- proj2Pair
  | proj2Pair hv₁ hv₂ =>
      cases ht with
      | proj2Ty h =>
          cases h with
          | pair h₁ h₂ =>
              exact h₂

end STLC