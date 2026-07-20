import TypeSystemsInLean.PLFABased.Syntax
import TypeSystemsInLean.PLFABased.Rename
import TypeSystemsInLean.PLFABased.Substitution

/-!
# Lemmas

This file contains auxiliary lemmas for renaming and substitution.

The lemmas are divided into two categories:

* PLFA-derived lemmas
  - Correspond directly to lemmas appearing in the PLFA
    *Programming Language Foundations in Agda*.

* Lean helper lemmas
  - Auxiliary lemmas introduced to simplify proofs in Lean.
    They do not necessarily appear explicitly in PLFA.

The correspondence with PLFA is documented for each lemma where applicable.
-/

/-!
# 補題

このファイルでは rename と substitution に関する補題を証明する。

補題は次の2種類に分類する。

* PLFA由来の補題
  - PLFA (*Programming Language Foundations in Agda*)
    に直接対応する補題。

* Lean実装用の補助補題
  - Leanで証明を簡潔にするために追加した補題。
    PLFAには同名では登場しない場合がある。

PLFAに対応する補題については、
各補題のコメントで対応箇所を明記する。
-/

namespace STLC

open Term

------------------------------------------------------------
-- Substitution lemmas
------------------------------------------------------------

/--
The identity substitution.
-/

/-
恒等置換。

各変数を自分自身へ写す置換。
-/
def idsSub : Subst :=
  fun x => #x

/--
The extension of the identity substitution is the identity substitution.

Corresponds to `exts-ids` in the PLFA Substitution chapter.
-/

/-
恒等置換を拡張しても、
再び恒等置換になる。

【PLFA対応】

PLFA Substitution 章の
`exts-ids`
に対応する補題。
-/
theorem exts_ids :
    exts idsSub = idsSub := by
  funext x
  cases x with
  | zero =>
      rfl
  | succ n =>
      simp [exts, idsSub, rename, shift]

/--
Applying the identity substitution leaves a term unchanged.

Corresponds to `sub-id` in the PLFA Substitution chapter.
-/

/-
恒等置換を適用しても、
項は変化しない。

【PLFA対応】

PLFA Substitution 章の
`sub-id`
に対応する補題。
-/
theorem subst_ids :
    ∀ t : Term,
      t⟦idsSub⟧ = t := by
  intro t
  induction t with
  | var x =>
      rfl

  | lam t ih =>
      simp [subst]
      rw [exts_ids]
      exact ih

  | ap t u iht ihu =>
      simp [subst, iht, ihu]


------------------------------------------------------------
-- Interaction between renaming and substitution
------------------------------------------------------------

/--
Extension commutes with mapping a renaming over a substitution.

This lemma is used in the proof of `rename_subst`.
-/

/-
置換へのリネーム作用と、置換の拡張は可換である。

【Lean実装用の補助補題】

`rename_subst` のラムダ抽象ケースで利用する。
-/
theorem exts_mapSubst
    (ρ : Renaming)
    (σ : Subst) :
    exts (mapSubst ρ σ)
      =
    mapSubst (ext ρ) (exts σ) := by
  funext x
  cases x with
  | zero =>
      rfl

  | succ n =>
      simp [exts, mapSubst]
      -- rw [show ((σ n)⟪ρ⟫)⟪shift⟫ = (σ n)⟪shift ∘r ρ⟫ by
            -- simpa using (rename_comp (σ n) ρ shift)]
      -- rw [shift_ext]
      -- rw [show (σ n)⟪ext ρ ∘r shift⟫ = ((σ n)⟪shift⟫)⟪ext ρ⟫ by
            -- symm
            -- simpa using (rename_comp (σ n) shift (ext ρ))]
      calc
            ((σ n)⟪ρ⟫)⟪shift⟫
                = (σ n)⟪shift ∘r ρ⟫ := by
                    simpa using (rename_comp (σ n) ρ shift)
            _ = (σ n)⟪ext ρ ∘r shift⟫ := by
                    rw [shift_ext]
            _ = ((σ n)⟪shift⟫)⟪ext ρ⟫ := by
                    symm
                    simpa using (rename_comp (σ n) shift (ext ρ))

/--
Renaming after substitution.

Corresponds to `rename-subst`
in the PLFA Substitution chapter.
-/

/-
置換後にリネームを適用する補題。

【PLFA対応】

PLFA Substitution 章の
`rename-subst`
に対応する。
-/
theorem rename_subst :
    ∀ (t : Term)
      (σ : Subst)
      (ρ : Renaming),
      (t⟦σ⟧)⟪ρ⟫ =
      t⟦mapSubst ρ σ⟧ := by
  intro t
  induction t with
  | var x =>
      intro σ ρ
      rfl

  | lam t ih =>
      intro σ ρ
      simp [subst, rename]
      rw [exts_mapSubst]
      exact ih (exts σ) (ext ρ)

  | ap t u iht ihu =>
      intro σ ρ
      simp [subst, rename, iht, ihu]



end STLC