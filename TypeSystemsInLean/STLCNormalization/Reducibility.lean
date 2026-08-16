import TypeSystemsInLean.STLCProducts.Soundness

namespace STLC

/-
This file begins the normalization proof for the Simply Typed Lambda Calculus.

The proof follows the computability method (logical relations) presented in
Types and Programming Languages (TaPL), while building on the STLC
implementation developed in the PLFA style.

The first step is to define what it means for a term to normalize.
-/

/-
【TaPL・PLFA対応】

停止性証明では、まず「項が停止する」とは何かを定義する。

型健全性では

    「型付き項は stuck にならない」

ことを示したが、停止性ではさらに強く

    「型付き項は必ず値まで評価される」

ことを示す。

そのため最初に `Normalizes` を定義し、
後に Computability Predicate（Reducibility）を型ごとに定義していく。
-/

/--
A term normalizes if it evaluates to some value in zero or more steps.
-/
def Normalizes (t : Term) : Prop :=
  ∃ v, t ⟶* v ∧ Value v

/-
【PLFA対応】

`Normalizes t` は、

    t ⟶* v

となる値 `v` が存在することを表す。

ここで `⟶*` は reflexive-transitive closure（多段階評価）であり、
0回以上の評価によって値へ到達できることを意味する。

この述語が、後に定義する Reducibility の土台となる。
-/

/--
Every value trivially normalizes because it can reach itself in zero steps.
-/
theorem value_normalizes {v : Term} (hv : Value v) :
    Normalizes v := by
  exact ⟨v, MultiStep.refl, hv⟩

/-
The computability predicate (Reducibility).

This predicate is defined by induction on types.
It characterizes the terms that behave well at each type and
forms the foundation of the normalization proof.
-/

/-
【TaPL対応】

ここから Computability Predicate（Reducibility）を定義する。

TaPLでは、停止性を直接証明するのではなく、

    「各型で計算可能な項」

という述語を型の構造に沿って定義する。

その後、

    型付き項 ⇒ Reducible

を示すことで停止性を導く。
-/

/--
`Reducible A t` means that the term `t` is computable at type `A`.
-/
def Reducible : Ty → Term → Prop
  | .base, t =>
      Normalizes t

  | .prod A B, t =>
      Normalizes t ∧
      Reducible A (Term.proj1 t) ∧
      Reducible B (Term.proj2 t)

  | .arr A B, t =>
      Normalizes t ∧
      ∀ u, Reducible A u → Reducible B (t □ u)
/-
【TaPL対応】

各型での意味は次の通り。

- base
    基底型では停止することだけを要求する。

- prod
    `proj1` と `proj2` の結果が、それぞれの型で
    Computable であることを要求する。

- arr
    任意の Computable な引数に適用すると、
    結果も Computable になることを要求する。

特に関数型の定義は、後に証明する
Fundamental Theorem の中心となる。
-/


/-
Every reducible term normalizes.

This is the first fundamental property of the computability predicate.

Since `Normalizes` is built into every case of `Reducible`,
the proof is a straightforward induction on the structure of types.
-/

/-
【TaPL対応】

Computability Predicate が本当に停止性を含んでいることを示す最初の補題。

`Reducible` の定義では、

- base
- prod
- arr

のすべてのケースに `Normalizes` が含まれている。

そのため、この補題は型に関する帰納法だけで証明できる。

この補題は後に証明する Fundamental Theorem の土台となる。
-/

/--
Every reducible term eventually evaluates to a value.
-/
theorem reducible_normalizes :
    ∀ {A t}, Reducible A t → Normalizes t
  | .base, _, h =>
      h

  | .prod _ _, _, h =>
      h.1

  | .arr _ _, _, h =>
      h.1

/-
【TaPL対応】

各ケースは `Reducible` の定義をそのまま取り出すだけである。

- base : `Reducible = Normalizes`
- prod : `(Normalizes ∧ …)` の第1成分を取り出す。
- arr  : `(Normalizes ∧ …)` の第1成分を取り出す。

これにより、以後の証明では
「Reducible なら停止する」を自由に利用できるようになる。
-/

end STLC