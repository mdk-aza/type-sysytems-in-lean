import TypeSystemsInLean.SimpleSTLC.Syntax

namespace STLC

open Term

inductive Ty where
| base : Ty
| arr : Ty → Ty → Ty
deriving DecidableEq, Repr

infixr:60 " ⇒ " => Ty.arr

abbrev BContext := List Ty

inductive Lookup : BContext → Index → Ty → Prop where
| here
    {Γ : BContext}
    {A : Ty}
    :
    Lookup (A :: Γ) 0 A

  | there
    {Γ : BContext}
    {A B : Ty}
    {x : Index}
    :
      Lookup Γ x A →
      Lookup (B :: Γ) (x + 1) A

abbrev FContext := List (String × Ty)

inductive FLookup : FContext → String → Ty → Prop where
  | here
    {Γ : FContext}
    {A : Ty}
    {x : String}
    :
      FLookup ((x, A) :: Γ) x A

  | there
    {Γ : FContext}
    {A B : Ty}
    {x y: String}
    :
      x ≠ y →
      FLookup Γ x A →
      FLookup ((y, B) :: Γ) x A


inductive HasType :
    BContext → FContext → Term → Ty → Prop where

  | var
    {Γ : BContext}
    {Δ : FContext}
    {A : Ty}
    {x : Index}
    :
      Lookup Γ x A →
      HasType Γ Δ (Term.var (Var.bound x)) A

  | fvar
    {Γ : BContext}
    {Δ : FContext}
    {A : Ty}
    {x : String}
    :
      FLookup Δ x A →
      HasType Γ Δ (Term.var (Var.free x)) A

  | lam
    {Γ : BContext}
    {Δ : FContext}
    {t : Term}
    {A B: Ty}
    :
      HasType (A :: Γ) Δ t B →
      HasType Γ Δ (Term.lam t) (A ⇒ B)

  | ap
    {Γ : BContext}
    {Δ : FContext}
    {t u: Term}
    {A B: Ty}
    :
      HasType Γ Δ t (A ⇒ B) →
      HasType Γ Δ u A →
      HasType Γ Δ (Term.ap t u) B

end STLC
