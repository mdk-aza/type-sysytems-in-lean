import TypeSystemsInLean.PLFABased.Typing
import TypeSystemsInLean.PLFABased.Evaluation
import TypeSystemsInLean.PLFABased.Preservation
import TypeSystemsInLean.PLFABased.Progress

namespace STLC

open Term

/-- Reflexive-transitive closure of one-step reduction. -/
inductive MultiStep : Term → Term → Prop where
| refl :
    MultiStep t t
| trans :
    t ⟶ u →
    MultiStep u v →
    MultiStep t v

infix:50 " ⟶* " => MultiStep

/-- A term is in normal form if it cannot take a step. -/
def Normal (t : Term) : Prop :=
  ∀ u, ¬ (t ⟶ u)

/-- A stuck term is a normal form that is not a value. -/
def Stuck (t : Term) : Prop :=
  Normal t ∧ ¬ Value t

/-- Preservation for multi-step reduction. -/
theorem preservation_star
    {Γ : Context}
    {t u : Term}
    {A : Ty}
    (ht : Γ ⊢ t : A)
    (hs : t ⟶* u) :
    Γ ⊢ u : A := by
  induction hs with
  | refl =>
      simpa using ht

  | trans hstep hmulti ih =>
      exact ih (preservation ht hstep)

/-- Well-typed terms never get stuck. -/
theorem soundness
    {t u : Term}
    {A : Ty}
    (ht : [] ⊢ t : A)
    (hm : t ⟶* u) :
    ¬ Stuck u := by
  intro hs
  rcases hs with ⟨hnormal, hnotvalue⟩

  have hu : [] ⊢ u : A :=
    preservation_star ht hm

  have hp := progress hu rfl

  cases hp with
  | done hv =>
      exact hnotvalue hv

  | step hs =>
      exact (hnormal _ hs).elim

end STLC