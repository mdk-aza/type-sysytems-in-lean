import TypeSystemsInLean.PLFABased.Syntax
import TypeSystemsInLean.PLFABased.Rename

namespace STLC

open Term

------------------------------------------------------------
-- Substitution
------------------------------------------------------------

/--
A substitution maps each de Bruijn index to a term.
-/

/-
置換 (substitution) を表す。

`σ : Index → Term` は、
各 de Bruijn index をどの項に置き換えるかを表す写像である。
-/
abbrev Subst := Index → Term

/--
Extend a substitution under a lambda abstraction.

The newly bound variable (`#0`) is left unchanged.
All remaining substituted terms are shifted to avoid
variable capture.
-/

/-
ラムダ抽象の内部で置換を1段拡張する。

新しく束縛された変数 `#0` は置換しない。

それ以外の変数については、置換後の項を
1段持ち上げ (`shift`) ることで、
変数捕獲 (variable capture) を防ぐ。
-/
def exts (σ : Subst) : Subst
| 0     => #0
| n + 1 => (σ n)⟪shift⟫

/--
Apply a substitution to a term.

Variables are replaced according to the substitution `σ`.
When entering a lambda abstraction, the substitution is extended
using `exts` so that the newly bound variable (`#0`) remains bound.

This definition forms the basis of β-reduction and the
Substitution Lemma.
-/

/-
項全体に置換 (substitution) を適用する。

変数は置換写像 `σ` に従って置き換える。

ラムダ抽象の内部では、新しく束縛された変数 `#0`
はそのまま束縛変数として扱う必要があるため、
`exts` により置換を1段拡張して再帰的に適用する。

この定義は

    β簡約
        ↓
    置換補題 (Substitution Lemma)
        ↓
    型保存性 (Preservation)

の土台となる。
-/
def subst (σ : Subst) : Term → Term
| .var x =>
    -- Replace a variable according to the substitution.
    -- 変数は置換写像に従って置き換える。
    σ x

| .lam t =>
    -- Enter a binder.
    -- Extend the substitution so that #0 remains bound.
    --
    -- ラムダ抽象に入ると新しい束縛変数 #0 が増える。
    -- exts によって置換を拡張して再帰する。
    .lam (subst (exts σ) t)

| .ap t u =>
    -- Apply the substitution independently to both subterms.
    --
    -- 関数適用は左右の部分項へ独立に置換を適用する。
    .ap (subst σ t)
        (subst σ u)

/--
Apply a renaming to every term produced by a substitution.

This is the action of a renaming on substitutions.
-/

/-
置換が生成する各項にリネームを適用する。

言い換えると、
置換の値域（各項）に対してリネームを作用させる。

【Lean実装用の補助】

PLFAでは明示的な定義としては現れないが、
`rename-subst` や `subst-comp` を読みやすく記述するための補助定義である。
-/
def mapSubst (ρ : Renaming) (σ : Subst) : Subst :=
  fun x => (σ x)⟪ρ⟫

------------------------------------------------------------
-- Single substitution
------------------------------------------------------------

/--
Substitute a single term for variable `#0`.

Variables greater than `#0` are decremented because one
binder is removed.
-/

/-
変数 `#0` を1つの項で置き換える置換。

β簡約

    (λ t) v

を

    t[v/#0]

へ変換するときに用いる。

ラムダが1つ取り除かれるため、
残りの変数番号は1だけ小さくなる。
-/
def single (v : Term) : Subst
| 0     => v
| n + 1 => #n

------------------------------------------------------------
-- Notation
------------------------------------------------------------

/--
Notation for applying a substitution to a term.
-/

/-
置換を適用するための記法。

`t⟦σ⟧` は
「項 `t` に置換 `σ` を適用する」
ことを表す。
-/
notation t "⟦" σ "⟧" => subst σ t

end STLC