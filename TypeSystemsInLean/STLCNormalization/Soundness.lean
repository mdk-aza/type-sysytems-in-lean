import TypeSystemsInLean.STLCNormalization.Typing
import TypeSystemsInLean.STLCNormalization.Evaluation
import TypeSystemsInLean.STLCNormalization.Preservation
import TypeSystemsInLean.STLCProducts.Progress

namespace STLC

open Term

/-
Reflexive-transitive closure of one-step reduction.

One-step reduction (⟶) describes a single evaluation step.
Multi-step reduction (⟶*) extends this to zero or more steps.

一段階簡約 (⟶) の反射推移閉包。

一段階簡約を 0 回以上繰り返した関係を表す。
-/
inductive MultiStep : Term → Term → Prop where
| refl :
    MultiStep t t
| trans :
    t ⟶ u →
    MultiStep u v →
    MultiStep t v

infix:50 " ⟶* " => MultiStep

/-
A term is in normal form if no evaluation rule applies.

正規形 (Normal Form)。

これ以上評価規則を適用できない項を表す。
-/
def Normal (t : Term) : Prop :=
  ∀ u, ¬ (t ⟶ u)

/-
A stuck term is a normal form that is not a value.

A stuck term cannot continue evaluation,
although it has not reached a final result.

スタックした項。

評価できず、かつ値でもない項を表す。
型安全性では、このような状態に到達しないことを示す。
-/
def Stuck (t : Term) : Prop :=
  Normal t ∧ ¬ Value t

/-
Preservation extended to multi-step reduction.

If
    Γ ⊢ t : A
and
    t ⟶* u

then
    Γ ⊢ u : A

Preservation を多段簡約へ拡張した定理。

一段階簡約で型が保存されるなら、
0 回以上の簡約でも型は保存される。
-/
theorem preservation_star
    {Γ : Context}
    {t u : Term}
    {A : Ty}
    (ht : Γ ⊢ t : A)
    (hs : t ⟶* u) :
    Γ ⊢ u : A := by
  induction hs with
  | refl =>
      -- Zero reduction steps.
      -- 簡約を一度も行わない場合。
      simpa using ht

  | trans hstep hmulti ih =>
      -- Apply one-step preservation,
      -- then use the induction hypothesis.
      --
      -- 一段階 Preservation を適用し，
      -- 残りは帰納法の仮定を用いる。
      exact ih (preservation ht hstep)

/-
Type Soundness.

A well-typed closed term never gets stuck.

Proof outline:

1. Preservation guarantees that every reduct remains well typed.
2. Progress guarantees that every well-typed closed term is
   either a value or can take another evaluation step.
3. Therefore, a stuck term can never be reached.

型安全性 (Type Soundness)。

型付けされた閉じた項は決して stuck にならない。

証明の流れ：

1. Preservation により簡約後も型が保存される。
2. Progress により閉じた型付き項は
   「値」または「さらに簡約可能」のどちらかである。
3. よって stuck な状態には到達できない。
-/
theorem soundness
    {t u : Term}
    {A : Ty}
    (ht : [] ⊢ t : A)
    (hm : t ⟶* u) :
    ¬ Stuck u := by
  intro hs
  rcases hs with ⟨hnormal, hnotvalue⟩

  -- u remains well typed by Preservation.
  -- Preservation により u も型付け可能。
  have hu : [] ⊢ u : A :=
    preservation_star ht hm

  -- Progress classifies u as either
  -- a value or reducible.
  --
  -- Progress により u は
  -- 「値」または「簡約可能」のどちらか。
  have hp := progress hu rfl

  cases hp with
  | done hv =>
      -- Contradiction:
      -- a stuck term cannot be a value.
      --
      -- stuck は値ではないので矛盾。
      exact hnotvalue hv

  | step hs =>
      -- Contradiction:
      -- a stuck term cannot reduce.
      --
      -- stuck は簡約できないので矛盾。
      exact (hnormal _ hs).elim

end STLC