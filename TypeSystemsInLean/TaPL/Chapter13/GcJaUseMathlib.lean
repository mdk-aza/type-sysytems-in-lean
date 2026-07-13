/-
  Exercise 13.3.1 (TAPL) — Modeling garbage collection (Mathlib version).
  TAPL 練習問題 13.3.1 —— GCのモデル化（Mathlib 使用・簡約版）。

  Same statement and proof architecture as the Mathlib-free version, but
  golfed using Mathlib's `List.Subset` API, `split_ifs`, `omega`, and
  `simp`/`aesop` automation.  Memory is modeled as infinite (footnote †5),
  so clause (5)-(b)-ii (memory exhaustion) does not arise.  No `sorry`.

  内容・証明の構成は Mathlib なし版と同じ。Mathlib の `List.Subset`
  （`⊆`）、`split_ifs`、`omega`、`simp`/`aesop` を使って行数を大きく削減した。
  メモリは無限としてモデル化（脚注†5）。`sorry` なし。
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Common

namespace GC

/- ---------------- syntax (de Bruijn) 構文 ---------------- -/

inductive Term where
  | var : Nat → Term
  | abs : Term → Term
  | app : Term → Term → Term
  | unit : Term
  | loc : Nat → Term          -- 実行時のみ出現するストア位置
  | ref : Term → Term
  | deref : Term → Term
  | assign : Term → Term → Term
  deriving DecidableEq, Repr

open Term

inductive IsValue : Term → Prop where
  | vabs : ∀ t, IsValue (abs t)
  | vunit : IsValue unit
  | vloc : ∀ l, IsValue (loc l)

/-- 添字シフト（`c` 以上を `d` だけ上げる） -/
def shift (d : Nat) : Nat → Term → Term
  | c, var k => if k ≥ c then var (k + d) else var k
  | c, abs t => abs (shift d (c + 1) t)
  | c, app t1 t2 => app (shift d c t1) (shift d c t2)
  | _, unit => unit
  | _, loc l => loc l
  | c, ref t => ref (shift d c t)
  | c, deref t => deref (shift d c t)
  | c, assign t1 t2 => assign (shift d c t1) (shift d c t2)

/-- 添字シフト（`c` 以上を 1 下げる；`substTop` 内でのみ安全に使う） -/
def unshift : Nat → Term → Term
  | c, var k => if k ≥ c then var (k - 1) else var k
  | c, abs t => abs (unshift (c + 1) t)
  | c, app t1 t2 => app (unshift c t1) (unshift c t2)
  | _, unit => unit
  | _, loc l => loc l
  | c, ref t => ref (unshift c t)
  | c, deref t => deref (unshift c t)
  | c, assign t1 t2 => assign (unshift c t1) (unshift c t2)

/-- `[j ↦ s] t` -/
def subst (j : Nat) (s : Term) : Term → Term
  | var k => if k = j then s else var k
  | abs t => abs (subst (j + 1) (shift 1 0 s) t)
  | app t1 t2 => app (subst j s t1) (subst j s t2)
  | unit => unit
  | loc l => loc l
  | ref t => ref (subst j s t)
  | deref t => deref (subst j s t)
  | assign t1 t2 => assign (subst j s t1) (subst j s t2)

/-- β代入：`(λ.t) v --> substTop v t` -/
def substTop (s t : Term) : Term := unshift 0 (subst 0 (shift 1 0 s) t)

/- ---------------- locations 出現する位置の集合 ---------------- -/

/-- 項の中に文字どおり出現する location たちのリスト（`locations(t)`）。 -/
def locations : Term → List Nat
  | var _ => []
  | abs t => locations t
  | app t1 t2 => locations t1 ++ locations t2
  | unit => []
  | loc l => [l]
  | ref t => locations t
  | deref t => locations t
  | assign t1 t2 => locations t1 ++ locations t2

-- shift/unshift は var しか触らないので locations は不変
theorem locations_shift (d c : Nat) (t : Term) : locations (shift d c t) = locations t := by
  induction t generalizing c with
  | var k => simp [shift]; split <;> rfl
  | unit | loc _ => rfl
  | _ => simp_all [shift, locations]

theorem locations_unshift (c : Nat) (t : Term) : locations (unshift c t) = locations t := by
  induction t generalizing c with
  | var k => simp [unshift]; split <;> rfl
  | unit | loc _ => rfl
  | _ => simp_all [unshift, locations]

/-- 代入は locations を「合体」させるだけ（新しく増やさない）。 -/
theorem locations_subst (j : Nat) (s t : Term) :
    locations (subst j s t) ⊆ locations s ++ locations t := by
  induction t generalizing j s with
  | var k => simp only [subst]; split <;> simp [List.subset_append_left, List.subset_append_right]
  | unit => simp [subst, locations]
  | loc l => intro x hx; exact List.mem_append.mpr (Or.inr hx)
  | abs t ih =>
      intro x hx
      simp only [subst, locations] at hx
      have := ih (j + 1) (shift 1 0 s) hx
      rwa [locations_shift] at this
  | app t1 t2 ih1 ih2 | assign t1 t2 ih1 ih2 =>
      intro x hx
      simp only [subst, locations, List.mem_append] at hx
      rcases hx with hx | hx
      · rcases List.mem_append.mp (ih1 j s hx) with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
      · rcases List.mem_append.mp (ih2 j s hx) with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h)))
  | ref t ih | deref t ih => simpa [subst, locations] using ih j s

theorem locations_substTop (s t : Term) :
    locations (substTop s t) ⊆ locations s ++ locations t := by
  intro x hx
  unfold substTop at hx
  rw [locations_unshift] at hx
  have h := locations_subst 0 (shift 1 0 s) t hx
  rwa [locations_shift] at h

/- ---------------- stores ストア ---------------- -/

abbrev Store := List (Nat × Term)

def dom (μ : Store) : List Nat := μ.map Prod.fst

def lookupOpt (μ : Store) (l : Nat) : Option Term :=
  match μ with
  | [] => none
  | (l', v) :: μ => if l' = l then some v else lookupOpt μ l

theorem mem_dom_cons (l' : Nat) (v : Term) (μ : Store) (l : Nat) :
    l ∈ dom ((l', v) :: μ) ↔ l = l' ∨ l ∈ dom μ := by simp [dom]

theorem mem_dom_iff_lookup (μ : Store) (l : Nat) :
    l ∈ dom μ ↔ ∃ v, lookupOpt μ l = some v := by
  induction μ with
  | nil => simp [dom, lookupOpt]
  | cons p μ ih =>
      obtain ⟨l', v'⟩ := p
      rw [mem_dom_cons]
      unfold lookupOpt
      split_ifs with h
      · simp [h]
      · have hne : l ≠ l' := fun he => h he.symm
        simp only [hne, false_or]; rw [ih]

/-- 場所 `l`（既存前提）の値を書き換える。 -/
def update (μ : Store) (l : Nat) (v : Term) : Store :=
  match μ with
  | [] => []
  | (l', v') :: μ => if l' = l then (l', v) :: μ else (l', v') :: update μ l v

theorem dom_update (μ : Store) (l : Nat) (v : Term) : dom (update μ l v) = dom μ := by
  induction μ with
  | nil => rfl
  | cons p μ ih => obtain ⟨l', v'⟩ := p; unfold update; split_ifs <;> simp_all [dom]

theorem lookup_update_same (μ : Store) (l : Nat) (v : Term) (hl : l ∈ dom μ) :
    lookupOpt (update μ l v) l = some v := by
  induction μ with
  | nil => simp [dom] at hl
  | cons p μ ih =>
      obtain ⟨l', v'⟩ := p
      unfold update; split_ifs with h
      · simp [lookupOpt, h]
      · simp only [lookupOpt, h, if_false]; exact ih (by simp [mem_dom_cons, h] at hl; tauto)

theorem lookup_update_other (μ : Store) (l l' : Nat) (v : Term) (hne : l' ≠ l) :
    lookupOpt (update μ l v) l' = lookupOpt μ l' := by
  induction μ with
  | nil => rfl
  | cons p μ ih =>
      obtain ⟨k, w⟩ := p
      unfold update; split_ifs with h
      · simp [lookupOpt, h, hne, hne.symm]
      · simp only [lookupOpt]; split_ifs <;> simp_all

/-- 場所 `l`（未使用前提）に初期値 `v` を新規確保。 -/
def alloc (μ : Store) (l : Nat) (v : Term) : Store := μ ++ [(l, v)]

theorem dom_alloc (μ : Store) (l : Nat) (v : Term) : dom (alloc μ l v) = dom μ ++ [l] := by
  simp [alloc, dom]

theorem lookup_alloc_same (μ : Store) (l : Nat) (v : Term) (hfresh : l ∉ dom μ) :
    lookupOpt (alloc μ l v) l = some v := by
  induction μ with
  | nil => simp [alloc, lookupOpt]
  | cons p μ ih =>
      obtain ⟨l1, v1⟩ := p
      simp only [mem_dom_cons, not_or] at hfresh
      simp only [alloc, List.cons_append, lookupOpt]
      rw [if_neg (Ne.symm hfresh.1)]
      exact ih hfresh.2

theorem lookup_alloc_other (μ : Store) (l l' : Nat) (v : Term) (hne : l' ≠ l) :
    lookupOpt (alloc μ l v) l' = lookupOpt μ l' := by
  induction μ with
  | nil => simp [alloc, lookupOpt, Ne.symm hne]
  | cons p μ ih =>
      obtain ⟨l1, v1⟩ := p
      simp only [alloc, List.cons_append, lookupOpt] at *
      split_ifs <;> simp_all

theorem mem_dom_alloc (μ : Store) (l l' : Nat) (v : Term) :
    l' ∈ dom (alloc μ l v) ↔ l' ∈ dom μ ∨ l' = l := by simp [alloc, dom]

theorem mem_dom_update (μ : Store) (l l' : Nat) (v : Term) :
    l' ∈ dom (update μ l v) ↔ l' ∈ dom μ := by rw [dom_update]

/- ---------------- reachability 到達可能性 ---------------- -/

/-- `l` に束縛された値の locations（未束縛なら `[]`）。 -/
def locOf (μ : Store) (l : Nat) : List Nat :=
  match lookupOpt μ l with
  | some v => locations v
  | none => []

/-- 根の集合 `roots` から `μ` を辿って到達可能な location たちの帰納的閉包。 -/
inductive ReachableFrom (roots : List Nat) (μ : Store) : Nat → Prop where
  | base {l} : l ∈ roots → ReachableFrom roots μ l
  | step {l l'} : ReachableFrom roots μ l → l' ∈ locOf μ l → ReachableFrom roots μ l'

def Reachable (t : Term) (μ : Store) (l : Nat) : Prop := ReachableFrom (locations t) μ l

theorem ReachableFrom.mono {roots1 roots2 : List Nat} (h : roots1 ⊆ roots2) {μ l}
    (hr : ReachableFrom roots1 μ l) : ReachableFrom roots2 μ l := by
  induction hr with
  | base hl => exact .base (h hl)
  | step _ hl' ih => exact .step ih hl'

theorem Reachable.mono {t1 t2 : Term} (h : locations t1 ⊆ locations t2) {μ l}
    (hr : Reachable t1 μ l) : Reachable t2 μ l := ReachableFrom.mono h hr

/-- 到達可能性は「到達可能な location での束縛」だけに依存する（局所性）。 -/
theorem ReachableFrom.agree {roots : List Nat} {μ1 μ2 : Store}
    (hagree : ∀ l, ReachableFrom roots μ1 l → lookupOpt μ1 l = lookupOpt μ2 l) {l}
    (hr : ReachableFrom roots μ1 l) : ReachableFrom roots μ2 l := by
  induction hr with
  | base hl => exact .base hl
  | @step l l' hprev hl' ih =>
      apply ReachableFrom.step ih
      unfold locOf at hl' ⊢; rwa [← hagree l hprev]

/-- (E-GC)：`μ'` はちょうど `µ` を `reachable(t, µ)` に制限したもの。 -/
def GCStep (t : Term) (μ μ' : Store) : Prop :=
  (∀ l, l ∈ dom μ' ↔ (l ∈ dom μ ∧ Reachable t μ l)) ∧
  (∀ l, l ∈ dom μ' → lookupOpt μ' l = lookupOpt μ l)

/- ---------------- ordinary evaluation 通常の評価 ---------------- -/

/-- `ref` は常にカウンタ `n` の位置に確保する（GC済みストアと未GC済み
    ストアが必ず同じ場所に割り当てるための仕組み；本文コメント参照）。 -/
inductive Step : Term → Nat → Store → Term → Nat → Store → Prop where
  | appAbs {t v n μ} : IsValue v → Step (app (abs t) v) n μ (substTop v t) n μ
  | app1 {t1 t1' t2 n n' μ μ'} : Step t1 n μ t1' n' μ' → Step (app t1 t2) n μ (app t1' t2) n' μ'
  | app2 {v1 t2 t2' n n' μ μ'} :
      IsValue v1 → Step t2 n μ t2' n' μ' → Step (app v1 t2) n μ (app v1 t2') n' μ'
  | refV {v n μ} : IsValue v → n ∉ dom μ → Step (ref v) n μ (loc n) (n + 1) (alloc μ n v)
  | ref1 {t t' n n' μ μ'} : Step t n μ t' n' μ' → Step (ref t) n μ (ref t') n' μ'
  | derefLoc {n μ l v} : lookupOpt μ l = some v → Step (deref (loc l)) n μ v n μ
  | deref1 {t t' n n' μ μ'} : Step t n μ t' n' μ' → Step (deref t) n μ (deref t') n' μ'
  | assignLoc {n μ l v} : IsValue v → l ∈ dom μ → Step (assign (loc l) v) n μ unit n (update μ l v)
  | assign1 {t1 t1' t2 n n' μ μ'} :
      Step t1 n μ t1' n' μ' → Step (assign t1 t2) n μ (assign t1' t2) n' μ'
  | assign2 {v1 t2 t2' n n' μ μ'} :
      IsValue v1 → Step t2 n μ t2' n' μ' → Step (assign v1 t2) n μ (assign v1 t2') n' μ'

inductive StepStar : Term → Nat → Store → Term → Nat → Store → Prop where
  | refl {t n μ} : StepStar t n μ t n μ
  | tail {t n μ t' n' μ' t'' n'' μ''} :
      StepStar t n μ t' n' μ' → Step t' n' μ' t'' n'' μ'' → StepStar t n μ t'' n'' μ''

theorem StepStar.single {t n μ t' n' μ'} (h : Step t n μ t' n' μ') : StepStar t n μ t' n' μ' :=
  StepStar.tail StepStar.refl h

theorem StepStar.trans {t1 n1 μ1 t2 n2 μ2 t3 n3 μ3}
    (h1 : StepStar t1 n1 μ1 t2 n2 μ2) (h2 : StepStar t2 n2 μ2 t3 n3 μ3) :
    StepStar t1 n1 μ1 t3 n3 μ3 := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact StepStar.tail ih hstep

/- ---------------- locality lemmas 局所性補題 ---------------- -/
/-  Step は評価中の項に「今まさに名前が書かれている」location しか
    触れない、ということを述べる3つの補題：
    (A) 定義域は縮まない　(B) 新規追加された location は評価後の項に出現
    (C) 値が変わった location は評価前の項に出現 -/

theorem Step.dom_mono {t n μ t' n' μ'} (h : Step t n μ t' n' μ') : dom μ ⊆ dom μ' := by
  induction h with
  | appAbs _ | derefLoc _ => exact List.Subset.refl _
  | refV _ _ => exact fun x hx => (mem_dom_alloc _ _ _ _).mpr (Or.inl hx)
  | assignLoc _ _ => simp [dom_update]
  | app1 _ ih | app2 _ _ ih | ref1 _ ih | deref1 _ ih | assign1 _ ih | assign2 _ _ ih => exact ih

theorem Step.new_loc_in_result {t n μ t' n' μ'} (h : Step t n μ t' n' μ') :
    ∀ l, l ∈ dom μ' → l ∉ dom μ → l ∈ locations t' := by
  induction h with
  | appAbs _ | derefLoc _ => intro l hl' hl; exact absurd hl' hl
  | assignLoc _ _ => intro l hl' hl; rw [mem_dom_update] at hl'; exact absurd hl' hl
  | app1 _ ih | assign1 _ ih => intro l hl' hl; exact List.mem_append_left _ (ih l hl' hl)
  | app2 _ _ ih | assign2 _ _ ih => intro l hl' hl; exact List.mem_append_right _ (ih l hl' hl)
  | ref1 _ ih | deref1 _ ih => intro l hl' hl; simpa [locations] using ih l hl' hl
  | @refV v n0 μ0 _ hfresh =>
      intro l hl' hl
      rcases (mem_dom_alloc μ0 n0 l v).mp hl' with h1 | h1
      · exact absurd h1 hl
      · subst h1; simp [locations]

theorem Step.changed_loc_in_source {t n μ t' n' μ'} (h : Step t n μ t' n' μ') :
    ∀ l, l ∈ dom μ → lookupOpt μ l ≠ lookupOpt μ' l → l ∈ locations t := by
  induction h with
  | appAbs _ | derefLoc _ => intro l _ hne; exact absurd rfl hne
  | app1 _ ih | assign1 _ ih => intro l hl hne; exact List.mem_append_left _ (ih l hl hne)
  | app2 _ _ ih | assign2 _ _ ih => intro l hl hne; exact List.mem_append_right _ (ih l hl hne)
  | ref1 _ ih | deref1 _ ih => intro l hl hne; simpa [locations] using ih l hl hne
  | @refV v n0 μ0 _ hfresh =>
      intro l hl hne
      have hne_ll0 : l ≠ n0 := fun he => hfresh (he ▸ hl)
      exact absurd (lookup_alloc_other μ0 n0 l v hne_ll0).symm hne
  | @assignLoc n0 μ0 l0 v _ _ =>
      intro l hl hne
      by_cases heq : l = l0
      · subst heq; simp [locations]
      · exact absurd (lookup_update_other μ0 l0 l v heq).symm hne

/- ---------------- boundedness 割り当てカウンタの有界性 ---------------- -/

/-- ストア中のすべての location が `n` 未満。`n`（以上）はまだ未使用。 -/
def Bounded (n : Nat) (μ : Store) : Prop := ∀ l ∈ dom μ, l < n

theorem Bounded.mono {n μ} (h : Bounded n μ) : n ∉ dom μ := fun hmem => (h n hmem).false
theorem Bounded.subset {n μ μ'} (h : Bounded n μ) (hsub : dom μ' ⊆ dom μ) : Bounded n μ' :=
  fun l hl => h l (hsub hl)

theorem Step.preserves_bounded {t n μ t' n' μ'} (h : Step t n μ t' n' μ')
    (hb : Bounded n μ) : n ≤ n' ∧ Bounded n' μ' := by
  induction h with
  | appAbs _ | derefLoc _ => exact ⟨le_refl _, hb⟩
  | @assignLoc n0 μ0 l0 v _ _ =>
      exact ⟨le_refl _, fun l hl => hb l ((mem_dom_update μ0 l0 l v).mp hl)⟩
  | @refV v n0 μ0 _ hfresh =>
      refine ⟨Nat.le_succ _, fun l hl => ?_⟩
      rcases (mem_dom_alloc μ0 n0 l v).mp hl with hl | hl
      · have := hb l hl; omega
      · omega
  | @app1 _ _ _ n n' _ _ _ ih | @app2 _ _ _ n n' _ _ _ _ ih
  | @ref1 _ _ n n' _ _ _ ih | @deref1 _ _ n n' _ _ _ ih
  | @assign1 _ _ _ n n' _ _ _ ih | @assign2 _ _ _ n n' _ _ _ _ ih => exact ih hb

theorem StepStar.preserves_bounded {t n μ t' n' μ'} (h : StepStar t n μ t' n' μ')
    (hb : Bounded n μ) : n ≤ n' ∧ Bounded n' μ' := by
  induction h with
  | refl => exact ⟨le_refl _, hb⟩
  | tail _ hstep ih =>
      obtain ⟨hle, hb'⟩ := ih
      obtain ⟨hle2, hb''⟩ := hstep.preserves_bounded hb'
      exact ⟨hle.trans hle2, hb''⟩

/- ---------------- "Safe" relation Safe 関係 ---------------- -/
/-  `Safe t n A B`：`A` は `n` で有界；`B ⊆ A`（定義域）；`B` は `t` の根を
    覆う；`B` は自己閉包（ポインタを辿っても `B` の外に出ない）；`B` は
    `A` と共通部分で一致。`GCStep` の結果はこの極端な（最小の）場合、
    「GC を一切しない」`B=A` はもう一方の極端な場合。 -/
def Safe (t : Term) (n : Nat) (A B : Store) : Prop :=
  Bounded n A ∧ dom B ⊆ dom A ∧ locations t ⊆ dom B ∧
  (∀ l ∈ dom B, ∀ l' ∈ locOf B l, l' ∈ dom B) ∧ (∀ l ∈ dom B, lookupOpt B l = lookupOpt A l)

theorem Safe.bounded {t n A B} (h : Safe t n A B) : Bounded n A := h.1
theorem Safe.dom_sub {t n A B} (h : Safe t n A B) : dom B ⊆ dom A := h.2.1
theorem Safe.roots_covered {t n A B} (h : Safe t n A B) : locations t ⊆ dom B := h.2.2.1
theorem Safe.self_closed {t n A B} (h : Safe t n A B) :
    ∀ l ∈ dom B, ∀ l' ∈ locOf B l, l' ∈ dom B := h.2.2.2.1
theorem Safe.agree {t n A B} (h : Safe t n A B) : ∀ l ∈ dom B, lookupOpt B l = lookupOpt A l :=
  h.2.2.2.2

/-- 自己閉包 + 根の被覆 ⟹ 到達可能な location はすべて `dom B` に入る。 -/
theorem Safe.reachable_in_dom {t n A B} (h : Safe t n A B) : ∀ l, Reachable t B l → l ∈ dom B := by
  intro l hr
  induction hr with
  | base hl => exact h.roots_covered hl
  | step hprev hl' ih => exact h.self_closed _ ih _ hl'

/-- 項を縮める方向への言い換えは常に安全（条件(3)以外は項に依存しない）。 -/
theorem Safe.reindex {t1 t2 n A B} (hsub : locations t2 ⊆ locations t1) (h : Safe t1 n A B) :
    Safe t2 n A B := ⟨h.bounded, h.dom_sub, fun _ hl => h.roots_covered (hsub hl), h.self_closed, h.agree⟩

theorem Safe.refl {t n A} (hb : Bounded n A) (hroots : locations t ⊆ dom A)
    (hclosed : ∀ l ∈ dom A, ∀ l' ∈ locOf A l, l' ∈ dom A) : Safe t n A A :=
  ⟨hb, List.Subset.refl _, hroots, hclosed, fun _ _ => rfl⟩

/-- 安全な側でさらに (E-GC) を行っても Safe は壊れない。 -/
theorem Safe.gc_absorb {t n A B C} (h : Safe t n A B) (hgc : GCStep t B C) : Safe t n A C := by
  have hreachB := h.reachable_in_dom
  refine ⟨h.bounded, fun l hl => h.dom_sub ((hgc.1 l).mp hl).1, fun l hl => ?_, fun l hl l' hl' => ?_, fun l hl => ?_⟩
  · exact (hgc.1 l).mpr ⟨h.roots_covered hl, .base hl⟩
  · have hlB := ((hgc.1 l).mp hl).1
    have hrl := ((hgc.1 l).mp hl).2
    have hl'B : l' ∈ locOf B l := by unfold locOf at hl' ⊢; rwa [hgc.2 l hl] at hl'
    exact (hgc.1 l').mpr ⟨hreachB _ (.step hrl hl'B), .step hrl hl'B⟩
  · rw [hgc.2 l hl, h.agree l ((hgc.1 l).mp hl).1]

/-- **"Up"補題。** 安全側 `B` が通常ステップを踏めるなら、大きい側 `A`
    も全く同じステップ（同じ項・同じカウンタ）を踏め、結果も Safe。 -/
theorem Safe.lift {t n B t' n' C} (hstep : Step t n B t' n' C) :
    ∀ A, Safe t n A B → ∃ A', Step t n A t' n' A' ∧ Safe t' n' A' C := by
  induction hstep with
  | @appAbs t0 v n μ hv =>
      intro A hSafe
      refine ⟨A, Step.appAbs hv, Safe.reindex (t1 := app (abs t0) v) ?_ hSafe⟩
      intro x hx
      have h1 := locations_substTop v t0 hx
      simpa [locations, List.mem_append, or_comm] using h1
  | @app1 t1 t1' t2 n n' μ μ' hsub ih =>
      intro A hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A
        (Safe.reindex (t1 := app t1 t2) (List.subset_append_left (locations t1) (locations t2)) hSafe)
      refine ⟨A', Step.app1 hstepA, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have ht2 : locations t2 ⊆ dom μ' :=
        fun x hx => Step.dom_mono hsub (hSafe.roots_covered (List.mem_append_right _ hx))
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hSafe'.roots_covered h
      · exact ht2 h
  | @app2 v1 t2 t2' n n' μ μ' hv1 hsub ih =>
      intro A hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A
        (Safe.reindex (t1 := app v1 t2) (List.subset_append_right (locations v1) (locations t2)) hSafe)
      refine ⟨A', Step.app2 hv1 hstepA, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have hv1' : locations v1 ⊆ dom μ' :=
        fun x hx => Step.dom_mono hsub (hSafe.roots_covered (List.mem_append_left _ hx))
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hv1' h
      · exact hSafe'.roots_covered h
  | @refV v n0 μ hv hfresh =>
      intro A hSafe
      have hnA : n0 ∉ dom A := hSafe.bounded.mono
      refine ⟨alloc A n0 v, Step.refV hv hnA, ?_, ?_, ?_, ?_, ?_⟩
      · intro l hl
        rcases (mem_dom_alloc _ n0 l v).mp hl with hl | hl
        · have := hSafe.bounded l hl; omega
        · omega
      · intro l hl
        rw [mem_dom_alloc] at hl ⊢
        exact hl.imp (hSafe.dom_sub ·) id
      · intro l hl
        simp only [locations, List.mem_singleton] at hl
        exact (mem_dom_alloc _ _ _ _).mpr (Or.inr hl)
      · intro l hl l' hl'
        rcases (mem_dom_alloc μ n0 l v).mp hl with hl | hl
        · have hlne : l ≠ n0 := fun he => hfresh (he ▸ hl)
          have heq : locOf (alloc μ n0 v) l = locOf μ l := by
            unfold locOf; rw [lookup_alloc_other _ _ _ _ hlne]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.self_closed l hl l' hl'))
        · have heq : locOf (alloc μ n0 v) l = locations v := by
            rw [hl]; unfold locOf; rw [lookup_alloc_same _ _ _ hfresh]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.roots_covered hl'))
      · intro l hl
        rcases (mem_dom_alloc μ n0 l v).mp hl with hl | hl
        · have hlne : l ≠ n0 := fun he => hfresh (he ▸ hl)
          rw [lookup_alloc_other _ _ _ _ hlne, hSafe.agree l hl, lookup_alloc_other _ _ _ _ hlne]
        · subst hl; rw [lookup_alloc_same _ _ _ hfresh, lookup_alloc_same _ _ _ hnA]
  | @ref1 t0 t0' n n' μ μ' hsub ih =>
      intro A hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe
      exact ⟨A', Step.ref1 hstepA, hSafe'⟩
  | @derefLoc n μ l0 v0 hlk =>
      intro A hSafe
      have hl0 : l0 ∈ dom μ := hSafe.roots_covered (by simp [locations])
      have hlkA : lookupOpt A l0 = some v0 := by rw [← hSafe.agree l0 hl0, hlk]
      refine ⟨A, Step.derefLoc hlkA, hSafe.bounded, hSafe.dom_sub, ?_, hSafe.self_closed, hSafe.agree⟩
      have hlocOf : locOf μ l0 = locations v0 := by unfold locOf; rw [hlk]
      exact fun x hx => hSafe.self_closed l0 hl0 x (hlocOf ▸ hx)
  | @deref1 t0 t0' n n' μ μ' hsub ih =>
      intro A hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe
      exact ⟨A', Step.deref1 hstepA, hSafe'⟩
  | @assignLoc n0 μ l0 v0 hv0 hl0mem =>
      intro A hSafe
      have hl0 : l0 ∈ dom μ := hSafe.roots_covered (by simp [locations])
      have hl0A : l0 ∈ dom A := hSafe.dom_sub hl0
      have hv0sub : locations v0 ⊆ dom μ :=
        fun x hx => hSafe.roots_covered (by simp [locations]; exact Or.inr hx)
      refine ⟨update A l0 v0, Step.assignLoc hv0 hl0A, ?_, ?_, ?_, ?_, ?_⟩
      · intro l hl; rw [dom_update] at hl; exact hSafe.bounded l hl
      · rw [dom_update, dom_update]; exact hSafe.dom_sub
      · intro x hx; cases hx
      · intro l hl l' hl'
        rw [dom_update] at hl ⊢
        by_cases heq : l = l0
        · rw [heq] at hl'
          have hlocOf : locOf (update μ l0 v0) l0 = locations v0 := by
            unfold locOf; rw [lookup_update_same _ _ _ hl0]
          exact hv0sub (hlocOf ▸ hl')
        · have hlocOf : locOf (update μ l0 v0) l = locOf μ l := by
            unfold locOf; rw [lookup_update_other _ _ _ _ heq]
          exact hSafe.self_closed l hl l' (hlocOf ▸ hl')
      · intro l hl
        rw [dom_update] at hl
        by_cases heq : l = l0
        · rw [heq, lookup_update_same _ _ _ hl0, lookup_update_same _ _ _ hl0A]
        · rw [lookup_update_other _ _ _ _ heq, hSafe.agree l hl, lookup_update_other _ _ _ _ heq]
  | @assign1 t1 t1' t2 n n' μ μ' hsub ih =>
      intro A hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A
        (Safe.reindex (t1 := assign t1 t2) (List.subset_append_left (locations t1) (locations t2)) hSafe)
      refine ⟨A', Step.assign1 hstepA, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have ht2 : locations t2 ⊆ dom μ' :=
        fun x hx => Step.dom_mono hsub (hSafe.roots_covered (List.mem_append_right _ hx))
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hSafe'.roots_covered h
      · exact ht2 h
  | @assign2 v1 t2 t2' n n' μ μ' hv1 hsub ih =>
      intro A hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A
        (Safe.reindex (t1 := assign v1 t2) (List.subset_append_right (locations v1) (locations t2)) hSafe)
      refine ⟨A', Step.assign2 hv1 hstepA, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have hv1' : locations v1 ⊆ dom μ' :=
        fun x hx => Step.dom_mono hsub (hSafe.roots_covered (List.mem_append_left _ hx))
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hv1' h
      · exact hSafe'.roots_covered h

/-- **"Down"補題。** `Safe.lift` の鏡像：大きい側 `A` が通常ステップを
    踏めるなら、安全な部分ストア `B` も同じステップを踏め、結果も Safe。 -/
theorem Safe.down {t n A t' n' A'} (hstep : Step t n A t' n' A') :
    ∀ B, Safe t n A B → ∃ C, Step t n B t' n' C ∧ Safe t' n' A' C := by
  induction hstep with
  | @appAbs t0 v n μ hv =>
      intro B hSafe
      refine ⟨B, Step.appAbs hv, Safe.reindex (t1 := app (abs t0) v) ?_ hSafe⟩
      intro x hx
      have h1 := locations_substTop v t0 hx
      simpa [locations, List.mem_append, or_comm] using h1
  | @app1 t1 t1' t2 n n' μ μ' hsub ih =>
      intro B hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B
        (Safe.reindex (t1 := app t1 t2) (List.subset_append_left (locations t1) (locations t2)) hSafe)
      refine ⟨C, Step.app1 hstepB, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have ht2 : locations t2 ⊆ dom C :=
        fun x hx => Step.dom_mono hstepB (hSafe.roots_covered (List.mem_append_right _ hx))
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hSafe'.roots_covered h
      · exact ht2 h
  | @app2 v1 t2 t2' n n' μ μ' hv1 hsub ih =>
      intro B hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B
        (Safe.reindex (t1 := app v1 t2) (List.subset_append_right (locations v1) (locations t2)) hSafe)
      refine ⟨C, Step.app2 hv1 hstepB, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have hv1' : locations v1 ⊆ dom C :=
        fun x hx => Step.dom_mono hstepB (hSafe.roots_covered (List.mem_append_left _ hx))
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hv1' h
      · exact hSafe'.roots_covered h
  | @refV v n0 μ hv hfresh =>
      intro B hSafe
      have hnB : n0 ∉ dom B := fun hmem => hfresh (hSafe.dom_sub hmem)
      refine ⟨alloc B n0 v, Step.refV hv hnB, ?_, ?_, ?_, ?_, ?_⟩
      · intro l hl
        rcases (mem_dom_alloc _ n0 l v).mp hl with hl | hl
        · have := hSafe.bounded l hl; omega
        · omega
      · intro l hl
        rw [mem_dom_alloc] at hl ⊢
        exact hl.imp (hSafe.dom_sub ·) id
      · intro l hl
        simp only [locations, List.mem_singleton] at hl
        exact (mem_dom_alloc _ _ _ _).mpr (Or.inr hl)
      · intro l hl l' hl'
        rcases (mem_dom_alloc B n0 l v).mp hl with hl | hl
        · have hlne : l ≠ n0 := fun he => hnB (he ▸ hl)
          have heq : locOf (alloc B n0 v) l = locOf B l := by
            unfold locOf; rw [lookup_alloc_other _ _ _ _ hlne]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.self_closed l hl l' hl'))
        · have heq : locOf (alloc B n0 v) l = locations v := by
            rw [hl]; unfold locOf; rw [lookup_alloc_same _ _ _ hnB]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.roots_covered hl'))
      · intro l hl
        rcases (mem_dom_alloc B n0 l v).mp hl with hl | hl
        · have hlne : l ≠ n0 := fun he => hnB (he ▸ hl)
          rw [lookup_alloc_other _ _ _ _ hlne, hSafe.agree l hl, lookup_alloc_other _ _ _ _ hlne]
        · subst hl; rw [lookup_alloc_same _ _ _ hnB, lookup_alloc_same _ _ _ hfresh]
  | @ref1 t0 t0' n n' μ μ' hsub ih =>
      intro B hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B hSafe
      exact ⟨C, Step.ref1 hstepB, hSafe'⟩
  | @derefLoc n μ l0 v0 hlk =>
      intro B hSafe
      have hl0 : l0 ∈ dom B := hSafe.roots_covered (by simp [locations])
      have hlkB : lookupOpt B l0 = some v0 := by rw [hSafe.agree l0 hl0, hlk]
      refine ⟨B, Step.derefLoc hlkB, hSafe.bounded, hSafe.dom_sub, ?_, hSafe.self_closed, hSafe.agree⟩
      have hlocOf : locOf B l0 = locations v0 := by unfold locOf; rw [hlkB]
      exact fun x hx => hSafe.self_closed l0 hl0 x (hlocOf ▸ hx)
  | @deref1 t0 t0' n n' μ μ' hsub ih =>
      intro B hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B hSafe
      exact ⟨C, Step.deref1 hstepB, hSafe'⟩
  | @assignLoc n0 μ l0 v0 hv0 hl0mem =>
      intro B hSafe
      have hl0 : l0 ∈ dom B := hSafe.roots_covered (by simp [locations])
      have hv0sub : locations v0 ⊆ dom B :=
        fun x hx => hSafe.roots_covered (by simp [locations]; exact Or.inr hx)
      refine ⟨update B l0 v0, Step.assignLoc hv0 hl0, ?_, ?_, ?_, ?_, ?_⟩
      · intro l hl; rw [dom_update] at hl; exact hSafe.bounded l hl
      · rw [dom_update, dom_update]; exact hSafe.dom_sub
      · intro x hx; cases hx
      · intro l hl l' hl'
        rw [dom_update] at hl ⊢
        by_cases heq : l = l0
        · rw [heq] at hl'
          have hlocOf : locOf (update B l0 v0) l0 = locations v0 := by
            unfold locOf; rw [lookup_update_same _ _ _ hl0]
          exact hv0sub (hlocOf ▸ hl')
        · have hlocOf : locOf (update B l0 v0) l = locOf B l := by
            unfold locOf; rw [lookup_update_other _ _ _ _ heq]
          exact hSafe.self_closed l hl l' (hlocOf ▸ hl')
      · intro l hl
        rw [dom_update] at hl
        by_cases heq : l = l0
        · rw [heq, lookup_update_same _ _ _ hl0, lookup_update_same _ _ _ hl0mem]
        · rw [lookup_update_other _ _ _ _ heq, hSafe.agree l hl, lookup_update_other _ _ _ _ heq]
  | @assign1 t1 t1' t2 n n' μ μ' hsub ih =>
      intro B hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B
        (Safe.reindex (t1 := assign t1 t2) (List.subset_append_left (locations t1) (locations t2)) hSafe)
      refine ⟨C, Step.assign1 hstepB, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have ht2 : locations t2 ⊆ dom C :=
        fun x hx => Step.dom_mono hstepB (hSafe.roots_covered (List.mem_append_right _ hx))
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hSafe'.roots_covered h
      · exact ht2 h
  | @assign2 v1 t2 t2' n n' μ μ' hv1 hsub ih =>
      intro B hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B
        (Safe.reindex (t1 := assign v1 t2) (List.subset_append_right (locations v1) (locations t2)) hSafe)
      refine ⟨C, Step.assign2 hv1 hstepB, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have hv1' : locations v1 ⊆ dom C :=
        fun x hx => Step.dom_mono hstepB (hSafe.roots_covered (List.mem_append_left _ hx))
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hv1' h
      · exact hSafe'.roots_covered h

/- ---------------- 最終定理 ---------------- -/

/-- 「`A` は `B` を拡張する」：模範解答 (5)-(a)/(5)-(b) が要求するストア関係。 -/
def Extends (A B : Store) : Prop := dom B ⊆ dom A ∧ ∀ l ∈ dom B, lookupOpt B l = lookupOpt A l

theorem Extends.refl (A : Store) : Extends A A := ⟨List.Subset.refl _, fun _ _ => rfl⟩
theorem Safe.extends {t n A B} (h : Safe t n A B) : Extends A B := ⟨h.dom_sub, h.agree⟩

/-- `→ ∪ →gc` の1ステップ。 -/
def CombinedStep (t : Term) (n : Nat) (μ : Store) (t' : Term) (n' : Nat) (μ' : Store) : Prop :=
  Step t n μ t' n' μ' ∨ (t' = t ∧ n' = n ∧ GCStep t μ μ')

/-- `CombinedStep` の反射推移閉包、すなわち `→gc*`。 -/
inductive CombinedStar : Term → Nat → Store → Term → Nat → Store → Prop where
  | refl {t n μ} : CombinedStar t n μ t n μ
  | tail {t n μ t' n' μ' t'' n'' μ''} :
      CombinedStar t n μ t' n' μ' → CombinedStep t' n' μ' t'' n'' μ'' → CombinedStar t n μ t'' n'' μ''

theorem StepStar.toCombined {t n μ t' n' μ'} (h : StepStar t n μ t' n' μ') :
    CombinedStar t n μ t' n' μ' := by
  induction h with
  | refl => exact CombinedStar.refl
  | tail _ hstep ih => exact CombinedStar.tail ih (Or.inl hstep)

/-- 合成評価（`→ ∪ →gc`）は、大きなストア `A` に対して Safe であれば、
    `A` からの純粋な通常評価として再生でき、結果も再び Safe。 -/
theorem CombinedStar.safe_lift {t n μ t' n' μ''} (h : CombinedStar t n μ t' n' μ'') :
    ∀ A, Safe t n A μ → ∃ A', StepStar t n A t' n' A' ∧ Safe t' n' A' μ'' := by
  induction h with
  | refl => intro A hSafe; exact ⟨A, StepStar.refl, hSafe⟩
  | tail _ hcs ih =>
      intro A hSafe
      obtain ⟨A1, hstar1, hSafe1⟩ := ih A hSafe
      cases hcs with
      | inl hstep =>
          obtain ⟨A', hstepA, hSafe'⟩ := Safe.lift hstep A1 hSafe1
          exact ⟨A', StepStar.tail hstar1 hstepA, hSafe'⟩
      | inr hgc =>
          obtain ⟨heqt, heqn, hgcstep⟩ := hgc
          subst heqt; subst heqn
          exact ⟨A1, hstar1, Safe.gc_absorb hSafe1 hgcstep⟩

/-- **定理 13.3.1(5)-(a)。** GC付き評価 `(t,μ)→gc*(t',μ'')` が可能なら、
    通常評価 `(t,μ)→*(t',μ')` も可能で、`μ'` は `μ''` を拡張する。 -/
theorem gc_correctness_5a {t : Term} {μ : Store} {n : Nat}
    (hbounded : Bounded n μ) (hroots : locations t ⊆ dom μ)
    (hclosed : ∀ l ∈ dom μ, ∀ l' ∈ locOf μ l, l' ∈ dom μ)
    {t' : Term} {n' : Nat} {μ'' : Store} (h : CombinedStar t n μ t' n' μ'') :
    ∃ μ', StepStar t n μ t' n' μ' ∧ Extends μ' μ'' := by
  obtain ⟨μ', hstar, hSafe⟩ := h.safe_lift μ (Safe.refl hbounded hroots hclosed)
  exact ⟨μ', hstar, hSafe.extends⟩

/-- **定理 13.3.1(5)-(b)（無限メモリ／メモリ安全の場合）。** 通常評価
    `(t,μ)→*(t',μ')` が可能なら、同じ `t'` に到達するGC付き評価
    `(t,μ)→gc*(t',μ'')` が存在し、`μ'` はその `μ''` を拡張する
    （メモリ無限なので (5)-(b)-(ii) の枯渇節は起こらない：脚注†5）。 -/
theorem gc_correctness_5b {t : Term} {n : Nat} {μ : Store} {t' : Term} {n' : Nat} {μ' : Store}
    (h : StepStar t n μ t' n' μ') : ∃ μ'', CombinedStar t n μ t' n' μ'' ∧ Extends μ' μ'' :=
  ⟨μ', h.toCombined, Extends.refl μ'⟩

end GC