import TypeSystemsInLean.STLCProducts.Typing
import TypeSystemsInLean.STLCProducts.Evaluation

/-!
# Progress

A well-typed closed term is either

* a value, or
* can take one evaluation step.

This is one half of the type safety theorem.
-/

/-!
# Progress（進行）

閉じた型付き項は

* 値である
* 1ステップ評価できる

のどちらかである。

型安全性定理の半分を構成する。
-/

namespace STLC

------------------------------------------------------------
-- Progress Result
------------------------------------------------------------

/--
Result of the progress theorem.
-/

/-
Progress の結果。

値であるか，
1ステップ評価できるかのどちらか。
-/
inductive Progress (t : Term) : Prop where
| done :
    Value t →
    Progress t

| step :
    ∀ {t'},
    t ⟶ t' →
    Progress t

------------------------------------------------------------
-- Progress Theorem
------------------------------------------------------------

/--
A well-typed closed term either is a value
or can take one evaluation step.
-/

/-
閉じた型付き項は

* 値
* 1ステップ評価可能

のどちらかである。
-/
theorem progress
    {Γ : Context}
    {t : Term}
    {A : Ty}
    (ht : Γ ⊢ t : A)
    (hΓ : Γ = []) :
    Progress t := by
     induction ht using HasType.recOn with
| var h =>
    cases hΓ
    exact False.elim (lookup_nil h)
  | lam h ih =>
      exact Progress.done (Value.lam _)
  | ap h₁ h₂ ih₁ ih₂ =>
      have pt := ih₁ hΓ
      have pu := ih₂ hΓ

      cases pt with
      | step hs =>
          exact Progress.step (Step.app₁ hs)

      | done hv =>
              cases pu with
              | step hs =>
                  exact Progress.step (Step.app₂ hv hs)

              | done hv₂ =>
                  cases hv with
                  | lam body =>
                      exact Progress.step (Step.beta hv₂)

                  | pair v₁ v₂ hv₁ hv₂ =>
                      -- A pair cannot have a function type.
                      cases h₁
    | pair h₁ h₂ ih₁ ih₂ =>
        have pt := ih₁ hΓ
        have pu := ih₂ hΓ

        cases pt with
        | step hs =>
            exact Progress.step (Step.pair₁ hs)

        | done hv₁ =>
          cases pu with
          | step hs =>
              exact Progress.step (Step.pair₂ hv₁ hs)

          | done hv₂ =>
              exact Progress.done (Value.pair _ _ hv₁ hv₂)

     | proj1Ty h ih =>
         have pt := ih hΓ

         cases pt with
         | step hs =>
             exact Progress.step (Step.proj1₁ hs)

         | done hv =>
             cases hv with
             | lam body =>
                 -- A lambda cannot have a product type.
                 cases h

             | pair v₁ v₂ hv₁ hv₂ =>
                 exact Progress.step (Step.proj1Pair hv₁ hv₂)

     | proj2Ty h ih =>
         have pt := ih hΓ

         cases pt with
         | step hs =>
             exact Progress.step (Step.proj2₁ hs)

         | done hv =>
             cases hv with
             | lam body =>
                 -- A lambda cannot have a product type.
                 cases h

             | pair v₁ v₂ hv₁ hv₂ =>
                 exact Progress.step (Step.proj2Pair hv₁ hv₂)

end STLC