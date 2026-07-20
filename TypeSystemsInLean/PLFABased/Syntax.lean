namespace STLC

/-
This file defines the abstract syntax of the Simply Typed Lambda Calculus
following Programming Language Foundations in Agda (PLFA).

Variables are represented using de Bruijn indices instead of names.
This eliminates α-conversion and simplifies renaming and substitution.
-/


/--
Variable indices represented using de Bruijn indices.

Instead of variable names, variables are identified by the
number of surrounding binders.
-/

/-
【PLFA対応】

本実装では変数名を持たず、
PLFA と同様に de Bruijn index を用いて変数を表現する。

de Bruijn index は

    #0  : 最も近い λ が束縛する変数
    #1  : 1つ外側の λ が束縛する変数
    #2  : さらに外側...

というように、束縛位置までの距離で変数を表す。

これにより α変換（変数名の付け替え）を考える必要がなくなり、
rename や substitution を単純な構造再帰として定義できる。
-/
abbrev Index := Nat

/--
Simply Typed Lambda Calculus terms (untyped syntax).

Variables are represented by de Bruijn indices.
-/

/-
【PLFA対応】

STLC の項（Term）の構文。

    t ::= x
        | λ.t
        | t t

をそのまま Lean の inductive として定義している。

変数は名前ではなく de Bruijn index を用いるため、

    λx.x

ではなく

    ƛ #0

のように表現する。

例えば

    λx.λy.x

は

    ƛ (ƛ #1)

となる。
-/
inductive Term where
| var : Index → Term
| lam : Term → Term
| ap  : Term → Term → Term
deriving DecidableEq, Repr

open Term

/-- Variable notation (#0, #1, ...). -/
prefix:90 "#" => Term.var
/-- Lambda notation (ƛ t). -/
prefix:60 "ƛ " => Term.lam
/-- Application notation (t □ u). -/
infixl:70 " □ " => Term.ap

/--
Values of the STLC.

Only lambda abstractions are values.
-/

/-
【PLFA対応】

値 (Value) の定義。

STLC では λ抽象のみを値とする。

    v ::= λ.t

変数や関数適用は値ではない。

この定義は Progress の証明で利用される。
-/


inductive Value : Term → Prop where
| VLam :
    ∀ {t},
    Value (ƛ t)

open Value

end STLC