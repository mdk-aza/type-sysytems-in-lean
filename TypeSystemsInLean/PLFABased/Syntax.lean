namespace STLC

abbrev Index := Nat

inductive Term where
| var : Index → Term
| lam : Term → Term
| ap  : Term → Term → Term
deriving DecidableEq, Repr

open Term

prefix:90 "#" => Term.var

prefix:60 "ƛ " => Term.lam

infixl:70 " □ " => Term.ap

inductive Value : Term → Prop where
| VLam :
    ∀ {t},
    Value (ƛ t)

open Value

end STLC