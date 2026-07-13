/-
  Exercise 13.3.1 (TAPL) — Modeling garbage collection.
  TAPL 練習問題 13.3.1 ——「ガベージコレクション（GC）」のモデル化。

  We formalize the fragment of "FullUntypedRef" relevant to Chapter 13
  (untyped call-by-value λ-calculus extended with mutable references),
  give it a small-step operational semantics threading an explicit store,
  add a garbage-collection step `→gc` exactly as described in the printed
  solution (13.3.1) using a semantic notion of *reachability*, and prove
  the correctness theorem that justifies the modification:

  第13章（参照）に関係する "FullUntypedRef" の断片
  （未型付き call-by-value λ計算 に、可変参照を追加したもの）を形式化し、
  ストア（ヒープ）を明示的に引き回すスモールステップ操作的意味論を与える。
  さらに、印刷された模範解答 (13.3.1) の記述どおりに、
  「到達可能性 (reachability)」という意味論的な概念を使って
  ガベージコレクションのステップ `→gc` を追加し、
  この変更を正当化する「正しさの定理」を証明する：

      (t, μ) →gc* (t', μ'')   implies   ∃ μ', (t, μ) →* (t', μ')
                                          and μ' ⊇ μ'' (domain-wise, agreeing
                                          on the common domain)                 [(5)-(a)]
      （GCありの評価が (t',μ'') に到達するならば、GCなしの評価も (t',μ') に
        到達でき、μ' は μ'' を「拡張」する——定義域が μ'' 以上あり、
        共通部分では値が一致する）

      (t, μ) →*     (t', μ')  implies   ∃ μ'', (t, μ) →gc* (t', μ'')
                                          and μ' ⊇ μ'' (domain-wise, agreeing
                                          on the common domain)                 [(5)-(b), memory-safe case]
      （逆に、GCなしの評価が (t',μ') に到達するならば、ある GCあり評価も
        同じ t' に到達でき、μ' は その μ'' を拡張する）

  Following the printed solution's own footnote (†5, from the errata),
  finiteness of the location set L is *not* required for this result; we
  therefore model the store's location set as all of `Nat`, i.e. memory is
  taken to be infinite.  This sidesteps clause (5)-(b)-ii (memory
  exhaustion), which the footnote explicitly says is an optional
  refinement, not a necessary one.  Everything below is proved with no
  `sorry`, using nothing beyond Lean 4's core library (no Mathlib).

  模範解答自身の脚注 (†5、正誤表より) にあるとおり、この結果を示すのに
  位置集合 L の有限性は「必須ではない」。そこでここではストアの位置集合を
  `Nat` 全体とし、メモリは無限であるとモデル化する。こうすることで
  (5)-(b)-(ii) 節（メモリ枯渇のケース）は自動的に回避される
  ——脚注が明言しているとおり、これは「必要な」精緻化ではなく
  「あってもよい」精緻化に過ぎない。以下はすべて `sorry` なしで証明されており、
  Lean 4 の core ライブラリ以外（Mathlib など）は一切使っていない。
-/

namespace GC

/- ============================================================ -/
/-  A little bit of list infrastructure (no Mathlib)             -/
/-  リストに関する下ごしらえ（Mathlib は使わない）                -/
/- ============================================================ -/

/-- "list inclusion" as a membership statement, spelled out so we don't
    need any library beyond `List.Mem`.
    「リストの包含関係」を素朴に「要素の所属」として定義したもの。
    `List.Mem`（`∈`）だけで書けるので、Mathlib の `⊆` 等は不要。 -/
def LSub (l1 l2 : List Nat) : Prop := ∀ x, x ∈ l1 → x ∈ l2

-- 反射律：l ⊆ l
theorem LSub.refl (l : List Nat) : LSub l l := fun _ h => h

-- 推移律：l1 ⊆ l2 かつ l2 ⊆ l3 ならば l1 ⊆ l3
theorem LSub.trans {l1 l2 l3 : List Nat} (h1 : LSub l1 l2) (h2 : LSub l2 l3) :
    LSub l1 l3 := fun x hx => h2 x (h1 x hx)

-- l1 ⊆ l1 ++ l2（左側の部分リストは連結全体に含まれる）
theorem LSub.appendLeft (l1 l2 : List Nat) : LSub l1 (l1 ++ l2) :=
  fun x hx => List.mem_append.mpr (Or.inl hx)

-- l2 ⊆ l1 ++ l2（右側の部分リストも連結全体に含まれる）
theorem LSub.appendRight (l1 l2 : List Nat) : LSub l2 (l1 ++ l2) :=
  fun x hx => List.mem_append.mpr (Or.inr hx)

-- 連結の合同性：両側で包含関係が保たれるなら、連結後も包含関係が保たれる
theorem LSub.appendCongr {l1 l2 l1' l2' : List Nat}
    (h1 : LSub l1 l1') (h2 : LSub l2 l2') : LSub (l1 ++ l2) (l1' ++ l2') := by
  intro x hx
  -- x ∈ l1 ++ l2 なら x ∈ l1 か x ∈ l2 のどちらか（List.mem_append で分解）
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append.mpr (Or.inl (h1 x h))
  · exact List.mem_append.mpr (Or.inr (h2 x h))

/- ============================================================ -/
/-  Syntax (de Bruijn indices, as is standard for mechanization) -/
/-  構文（形式化の定石どおり de Bruijn 添字を使う）                -/
/- ============================================================ -/

/-- Terms of the untyped λ-calculus with `unit` and mutable references.
    `loc l` is a run-time store location; it never occurs in source
    programs, only in terms that arise during evaluation.

    項の定義：unit と可変参照を持つ未型付きλ計算。
    `loc l` は実行時にのみ現れるストアの位置（location）で、
    ソースプログラム自体には出現せず、評価の途中で生成される項にのみ現れる。 -/
inductive Term where
  | var    : Nat → Term        -- 変数（de Bruijn 添字）
  | abs    : Term → Term        -- λ抽象（λ. t）
  | app    : Term → Term → Term -- 関数適用（t1 t2）
  | unit   : Term                -- unit 値
  | loc    : Nat → Term          -- 実行時のストア位置（プログラム中には出てこない）
  | ref    : Term → Term         -- 参照の生成（ref t）
  | deref  : Term → Term         -- 参照の中身を読む（!t）
  | assign : Term → Term → Term  -- 参照への代入（t1 := t2）
  deriving DecidableEq, Repr

open Term

/-- Values.
    値（評価が止まる項）：λ抽象、unit、ストア位置。 -/
inductive IsValue : Term → Prop where
  | vabs  : ∀ t, IsValue (abs t)
  | vunit : IsValue unit
  | vloc  : ∀ l, IsValue (loc l)

/- ---------------- shifting ---------------- -/
/- ---------------- 添字のシフト ---------------- -/

/-- Shift free variables (de Bruijn index ≥ `c`) up by `d`.
    自由変数（添字が `c` 以上のもの）の添字を `d` だけ上にずらす。
    λ抽象の中に入るたびにカットオフ `c` を 1 増やす、という
    de Bruijn 表現の標準的な shift 関数。 -/
def shift (d : Nat) : Nat → Term → Term
  | c, var k      => if k ≥ c then var (k + d) else var k
  | c, abs t      => abs (shift d (c + 1) t)
  | c, app t1 t2  => app (shift d c t1) (shift d c t2)
  | _, unit       => unit
  | _, loc l      => loc l          -- loc はただの数値ラベルなのでシフトの影響を受けない
  | c, ref t      => ref (shift d c t)
  | c, deref t    => deref (shift d c t)
  | c, assign t1 t2 => assign (shift d c t1) (shift d c t2)

/-- Shift free variables (index ≥ `c`) down by 1.  Used only in `substTop`,
    where it is applied to a term in which no free occurrence of index `c`
    remains (that occurrence having just been substituted away), so the
    shift is safe.

    自由変数（添字が `c` 以上のもの）の添字を 1 だけ下にずらす。
    `substTop` の中でのみ使われ、そこでは添字 `c` の自由な出現が
    （代入によって）ちょうど消えた後の項に対して適用されるので、
    この「下にずらす」操作は安全（負の添字が出ない）。 -/
def unshift : Nat → Term → Term
  | c, var k      => if k ≥ c then var (k - 1) else var k
  | c, abs t      => abs (unshift (c + 1) t)
  | c, app t1 t2  => app (unshift c t1) (unshift c t2)
  | _, unit       => unit
  | _, loc l      => loc l
  | c, ref t      => ref (unshift c t)
  | c, deref t    => deref (unshift c t)
  | c, assign t1 t2 => assign (unshift c t1) (unshift c t2)

/- ---------------- substitution ---------------- -/
/- ---------------- 代入 ---------------- -/

/-- `subst j s t` replaces free occurrences of variable `j` in `t` by `s`,
    adjusting indices as usual across binders.

    `subst j s t` は、項 `t` の中の自由変数 `j` の出現をすべて `s` で
    置き換える（束縛子をまたぐたびに、通常どおり添字を調整する）。 -/
def subst (j : Nat) (s : Term) : Term → Term
  | var k      => if k = j then s else var k
  | abs t      => abs (subst (j + 1) (shift 1 0 s) t)  -- λ の中に入るので j も s も 1 段シフト
  | app t1 t2  => app (subst j s t1) (subst j s t2)
  | unit       => unit
  | loc l      => loc l
  | ref t      => ref (subst j s t)
  | deref t    => deref (subst j s t)
  | assign t1 t2 => assign (subst j s t1) (subst j s t2)

/-- Beta-substitution at the top: `substTop s t` = `[0 ↦ s] t` used to
    implement `(λ.t) v --> substTop v t`.

    トップレベルでのベータ代入：`substTop s t` は `[0 ↦ s] t` を計算する。
    β簡約規則 `(λ.t) v --> substTop v t` を実装するために使う。
    手順は TAPL 6.1 の標準的なやり方：
    (1) s を 1 段シフトアップしてから t の変数 0 に代入し、
    (2) 最後に結果全体を 1 段シフトダウンして、
        束縛が 1 つ外れたことによる添字のズレを調整する。 -/
def substTop (s t : Term) : Term := unshift 0 (subst 0 (shift 1 0 s) t)

/- ============================================================ -/
/-  Locations occurring (syntactically) in a term                -/
/-  項の中に構文的に出現する位置（location）の集合                -/
/- ============================================================ -/

/-- `locations t` is the (possibly-repeating) list of store locations that
    literally occur in `t`.  This is `locations(t)` from the printed
    solution.

    `locations t` は、項 `t` の中に文字どおり出現するストア位置の
    リスト（重複があってもよい）。模範解答でいう `locations(t)` に対応する。
    集合として扱いたいだけなので、重複や順序は気にしない
    （すべて `List.Mem`（∈）だけで議論するため）。 -/
def locations : Term → List Nat
  | var _        => []
  | abs t        => locations t
  | app t1 t2    => locations t1 ++ locations t2
  | unit         => []
  | loc l        => [l]              -- loc l 自身がまさに「位置の出現」
  | ref t        => locations t
  | deref t      => locations t
  | assign t1 t2 => locations t1 ++ locations t2

/-- `shift`/`unshift` only ever touch `var` nodes, so they leave the set of
    occurring locations completely unchanged.

    `shift`／`unshift` は `var` ノードしか触らないので、
    出現する location の集合は完全に不変（等式で成り立つ）。 -/
theorem locations_shift (d c : Nat) (t : Term) :
    locations (shift d c t) = locations t := by
  induction t generalizing c with
  | var k => simp [shift, locations]; split <;> rfl
  | abs t ih => simp [shift, locations, ih]
  | app t1 t2 ih1 ih2 => simp [shift, locations, ih1, ih2]
  | unit => rfl
  | loc l => rfl
  | ref t ih => simp [shift, locations, ih]
  | deref t ih => simp [shift, locations, ih]
  | assign t1 t2 ih1 ih2 => simp [shift, locations, ih1, ih2]

-- 上と同様、unshift についても location の集合は不変
theorem locations_unshift (c : Nat) (t : Term) :
    locations (unshift c t) = locations t := by
  induction t generalizing c with
  | var k => simp [unshift, locations]; split <;> rfl
  | abs t ih => simp [unshift, locations, ih]
  | app t1 t2 ih1 ih2 => simp [unshift, locations, ih1, ih2]
  | unit => rfl
  | loc l => rfl
  | ref t ih => simp [unshift, locations, ih]
  | deref t ih => simp [unshift, locations, ih]
  | assign t1 t2 ih1 ih2 => simp [unshift, locations, ih1, ih2]

/-- Substitution can only ever *combine* the locations already present in
    the two pieces being glued together. For our purposes the inclusion
    direction is exactly what is needed.

    代入操作は、貼り合わせる2つの項がもともと持っていた location を
    「合体」させることしかできない（新しい location を生み出したりはしない）。
    今回必要なのは「⊆」の方向（新しく増えない、という保証）だけなので、
    等式ではなく包含関係として述べている。 -/
theorem locations_subst (j : Nat) (s t : Term) :
    LSub (locations (subst j s t)) (locations s ++ locations t) := by
  induction t generalizing j s with
  | var k =>
      simp only [subst]
      -- k = j かどうかで場合分け：s に置き換わるか、そのまま var k か
      split
      · intro x hx
        exact List.mem_append.mpr (Or.inl hx)
      · intro x hx
        exact List.mem_append.mpr (Or.inr hx)
  | abs t ih =>
      simp only [subst, locations]
      intro x hx
      -- λ の中に入るので shift された s を使う帰納法の仮定を利用
      -- （shift は locations を変えないので locations_shift で戻す）
      have hx' := ih (j + 1) (shift 1 0 s) x hx
      rw [locations_shift] at hx'
      exact hx'
  | app t1 t2 ih1 ih2 =>
      simp only [subst, locations]
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · rcases List.mem_append.mp (ih1 j s x h) with h' | h'
        · exact List.mem_append.mpr (Or.inl h')
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl h')))
      · rcases List.mem_append.mp (ih2 j s x h) with h' | h'
        · exact List.mem_append.mpr (Or.inl h')
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h')))
  | unit => intro x hx; cases hx
  | loc l => intro x hx; exact List.mem_append.mpr (Or.inr hx)
  | ref t ih =>
      simp only [subst, locations]
      exact ih j s
  | deref t ih =>
      simp only [subst, locations]
      exact ih j s
  | assign t1 t2 ih1 ih2 =>
      simp only [subst, locations]
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · rcases List.mem_append.mp (ih1 j s x h) with h' | h'
        · exact List.mem_append.mpr (Or.inl h')
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl h')))
      · rcases List.mem_append.mp (ih2 j s x h) with h' | h'
        · exact List.mem_append.mpr (Or.inl h')
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h')))

/-- Corollary: `locations (substTop s t) ⊆ locations s ++ locations t`.
    系：`locations (substTop s t) ⊆ locations s ++ locations t`。
    β簡約 `(λ.t0) v --> substTop v t0` を1回行っても、新しく現れる
    location は代入前の t0 と v がもともと持っていたもの以内に収まる、
    という事実（後で「安全なストア」を保つために何度も使う）。 -/
theorem locations_substTop (s t : Term) :
    LSub (locations (substTop s t)) (locations s ++ locations t) := by
  unfold substTop
  intro x hx
  rw [locations_unshift] at hx
  have h := locations_subst 0 (shift 1 0 s) t x hx
  rw [locations_shift] at h
  exact h

/- ============================================================ -/
/-  Stores                                                        -/
/-  ストア（ヒープ）                                                -/
/- ============================================================ -/

/-- A store is a finite association list from locations to (value) terms,
    exactly as in TAPL: `µ ∈ Store ::= {x1 = h1, ..., xn = hn}`.

    ストアは、TAPL そのままに、location から（値の）項への
    有限の連想リストとして表す：`µ ∈ Store ::= {x1 = h1, ..., xn = hn}`。 -/
abbrev Store := List (Nat × Term)

/-- Domain of a store.
    ストアの定義域（束縛されている location たちの集合）。 -/
def dom (μ : Store) : List Nat := μ.map Prod.fst

/-- Look up a location; `none` if unbound.  Earlier bindings shadow later
    ones, matching the usual convention for association lists.

    location を検索する。未束縛なら `none`。
    連想リストの通例どおり、先に出てくる束縛の方が優先される
    （後ろにある同じキーの束縛は隠される）。 -/
def lookupOpt (μ : Store) (l : Nat) : Option Term :=
  match μ with
  | [] => none
  | (l', v) :: μ => if l' = l then some v else lookupOpt μ l

-- 「dom への所属」を cons の形で書き下したもの（帰納法の補助）
theorem mem_dom_cons (l' : Nat) (v : Term) (μ : Store) (l : Nat) :
    l ∈ dom ((l', v) :: μ) ↔ l = l' ∨ l ∈ dom μ := by
  simp [dom]

-- 「dom に入っている」ことと「lookupOpt が some を返す」ことは同値
theorem mem_dom_iff_lookup (μ : Store) (l : Nat) :
    l ∈ dom μ ↔ ∃ v, lookupOpt μ l = some v := by
  induction μ with
  | nil => simp [dom, lookupOpt]
  | cons p μ ih =>
      obtain ⟨l', v'⟩ := p
      rw [mem_dom_cons]
      simp only [lookupOpt]
      by_cases h : l' = l
      · subst h; simp
      · simp only [h, if_false, ite_false]
        constructor
        · intro hh
          rcases hh with hh | hh
          · exact absurd hh.symm h
          · exact ih.mp hh
        · intro hh
          exact Or.inr (ih.mpr hh)

/-- Update the value bound to an already-present location `l`.
    すでに存在する location `l` に束縛された値を書き換える（代入 `l := v`）。 -/
def update (μ : Store) (l : Nat) (v : Term) : Store :=
  match μ with
  | [] => []
  | (l', v') :: μ => if l' = l then (l', v) :: μ else (l', v') :: update μ l v

-- update は「値」を書き換えるだけで、定義域（キーの集合）は変えない
theorem dom_update (μ : Store) (l : Nat) (v : Term) : dom (update μ l v) = dom μ := by
  induction μ with
  | nil => rfl
  | cons p μ ih =>
      obtain ⟨l', v'⟩ := p
      simp only [update]
      by_cases h : l' = l
      · simp [h, dom]
      · simp [h, dom] at ih ⊢
        exact ih

-- update した場所そのものを見れば、新しい値 v が入っている
theorem lookup_update_same (μ : Store) (l : Nat) (v : Term) (hl : l ∈ dom μ) :
    lookupOpt (update μ l v) l = some v := by
  induction μ with
  | nil => cases hl
  | cons p μ ih =>
      obtain ⟨l', v'⟩ := p
      simp only [update]
      by_cases h : l' = l
      · simp [h, lookupOpt]
      · simp only [h, if_false, ite_false]
        rw [mem_dom_cons] at hl
        have hl' : l ∈ dom μ := hl.resolve_left (fun he => h he.symm)
        simp only [lookupOpt, h, if_false, ite_false]
        exact ih hl'

/-- 更新した箇所とは違う場所を見れば、値は変わらない。
    （※このレンマの証明では `subst` を安易に使うと、生成された束縛変数
    `k`（cons パターンの先頭キー）ではなく、より前に導入されていた
    パラメータ `l` の方が消去されてしまう、という罠がある。
    そのため意図的に `rw`／`show` を使い、消去の向きを明示的に制御している。） -/
theorem lookup_update_other (μ : Store) (l l' : Nat) (v : Term) (hne : l' ≠ l) :
    lookupOpt (update μ l v) l' = lookupOpt μ l' := by
  induction μ with
  | nil => rfl
  | cons p μ ih =>
      rcases p with ⟨k, w⟩
      by_cases hk : k = l
      · -- k = l の場合：先頭の束縛が書き換えられる。l' ≠ l = k なので影響なし
        have hupd : update ((k, w) :: μ) l v = (k, v) :: μ := by
          unfold update; rw [if_pos hk]
        rw [hupd]
        have hkl' : ¬ k = l' := by rw [hk]; exact fun h => hne h.symm
        show (if k = l' then some v else lookupOpt μ l') = lookupOpt ((k, w) :: μ) l'
        rw [if_neg hkl']
        show lookupOpt μ l' = if k = l' then some w else lookupOpt μ l'
        rw [if_neg hkl']
      · -- k ≠ l の場合：先頭の束縛はそのまま、残りを再帰的に処理
        have hupd : update ((k, w) :: μ) l v = (k, w) :: update μ l v := by
          show (if k = l then (k, v) :: μ else (k, w) :: update μ l v) = (k, w) :: update μ l v
          rw [if_neg hk]
        rw [hupd]
        show (if k = l' then some w else lookupOpt (update μ l v) l')
            = (if k = l' then some w else lookupOpt μ l')
        by_cases hk' : k = l'
        · rw [if_pos hk', if_pos hk']
        · rw [if_neg hk', if_neg hk']
          exact ih

/-- Allocating `l` (assumed fresh) with initial value `v`.
    location `l`（未使用と仮定）に初期値 `v` を新規に割り当てる（新規確保）。
    リストの末尾に追加する実装（先頭検索の `lookupOpt` と組み合わせると、
    後から `update` された値がちゃんと見えることが保証される）。 -/
def alloc (μ : Store) (l : Nat) (v : Term) : Store := μ ++ [(l, v)]

-- 新規確保すると、定義域には l がちょうど1つ追加される
theorem dom_alloc (μ : Store) (l : Nat) (v : Term) :
    dom (alloc μ l v) = dom μ ++ [l] := by
  simp [alloc, dom]

-- 新しく確保した location l を検索すると、値 v が返る
theorem lookup_alloc_same (μ : Store) (l : Nat) (v : Term) (hfresh : l ∉ dom μ) :
    lookupOpt (alloc μ l v) l = some v := by
  induction μ with
  | nil => simp [alloc, lookupOpt]
  | cons p μ ih =>
      obtain ⟨l1, v1⟩ := p
      rw [mem_dom_cons] at hfresh
      have hfresh1 : l ≠ l1 := fun he => hfresh (Or.inl he)
      have hfresh2 : l ∉ dom μ := fun he => hfresh (Or.inr he)
      simp only [alloc, List.cons_append, lookupOpt]
      have h1 : l1 ≠ l := fun he => hfresh1 he.symm
      simp only [h1, if_false, ite_false]
      exact ih hfresh2

-- 新規確保しても、それ以外の場所の値は変わらない
theorem lookup_alloc_other (μ : Store) (l l' : Nat) (v : Term) (hne : l' ≠ l) :
    lookupOpt (alloc μ l v) l' = lookupOpt μ l' := by
  induction μ with
  | nil =>
      simp only [alloc, List.nil_append, lookupOpt]
      have : l ≠ l' := fun he => hne he.symm
      simp [this]
  | cons p μ ih =>
      obtain ⟨l1, v1⟩ := p
      simp only [alloc, List.cons_append, lookupOpt] at *
      by_cases h : l1 = l'
      · simp [h]
      · simp only [h, if_false, ite_false]
        exact ih

-- alloc 後の定義域への所属は「元から入っていた」か「今回追加した l」のどちらか
theorem mem_dom_alloc (μ : Store) (l l' : Nat) (v : Term) :
    l' ∈ dom (alloc μ l v) ↔ l' ∈ dom μ ∨ l' = l := by
  simp [alloc, dom]

-- alloc すると定義域は（真に）増える方向にしか変わらない
theorem LSub_dom_alloc (μ : Store) (l : Nat) (v : Term) : LSub (dom μ) (dom (alloc μ l v)) :=
  fun x hx => (mem_dom_alloc μ l x v).mpr (Or.inl hx)

theorem mem_dom_update (μ : Store) (l l' : Nat) (v : Term) :
    l' ∈ dom (update μ l v) ↔ l' ∈ dom μ := by rw [dom_update]

/- ============================================================ -/
/-  Reachability                                                  -/
/-  到達可能性                                                     -/
/- ============================================================ -/

/-- The locations occurring in the heap value bound to `l` (or `[]` if `l`
    is unbound).

    location `l` に束縛されているヒープ上の値に出現する location たち
    （`l` が未束縛なら `[]`）。「`l` から1歩でたどり着ける location たち」
    と読める。 -/
def locOf (μ : Store) (l : Nat) : List Nat :=
  match lookupOpt μ l with
  | some v => locations v
  | none   => []

/-- `ReachableFrom roots μ l` says `l` is reachable, in the store `μ`, from
    the given set (list) of root locations — exactly the inductive closure
    described in the printed solution: `l'` is reachable if it is a root,
    or if it is one step reachable (`l' ∈ locations(µ(l))`) from some
    already-reachable `l`.

    `ReachableFrom roots μ l` は、根の集合（リスト）`roots` から出発して、
    ストア `μ` の中で `l` にたどり着けることを表す——模範解答が述べている
    帰納的閉包そのもの：
    ・`base`：`l` が根に入っていれば、それだけで到達可能
    ・`step`：すでに到達可能な `l` の値の中に `l'` が現れていれば
      （`l' ∈ locOf μ l`）、`l'` も到達可能
    「前回の質問（GCの誤り）」で確認した反例のように、`base` だけでは
    足りず、この `step` によるポインタの追跡（推移閉包）が本質的に必要。 -/
inductive ReachableFrom (roots : List Nat) (μ : Store) : Nat → Prop where
  | base {l}  : l ∈ roots → ReachableFrom roots μ l
  | step {l l'} : ReachableFrom roots μ l → l' ∈ locOf μ l → ReachableFrom roots μ l'

/-- Reachability from a term `t` in a store `µ`: `reachable(t, µ)` from the
    printed solution.

    項 `t` からストア `µ` における到達可能性：模範解答の `reachable(t, µ)`
    に対応する。根の集合を「`t` の中に直接出てくる location たち」
    （＝ `locations t`）とした場合の `ReachableFrom`。 -/
def Reachable (t : Term) (μ : Store) (l : Nat) : Prop := ReachableFrom (locations t) μ l

/-- Reachability is monotone in the root set.
    到達可能性は根の集合について単調（根を増やせば到達可能な集合も増える）。 -/
theorem ReachableFrom.mono {roots1 roots2 : List Nat} (h : LSub roots1 roots2)
    {μ : Store} {l : Nat} (hr : ReachableFrom roots1 μ l) : ReachableFrom roots2 μ l := by
  induction hr with
  | base hl => exact .base (h _ hl)
  | step _ hl' ih => exact .step ih hl'

-- 上と同じことを「項の locations」の言葉で述べたもの
theorem Reachable.mono {t1 t2 : Term} (h : LSub (locations t1) (locations t2))
    {μ : Store} {l : Nat} (hr : Reachable t1 μ l) : Reachable t2 μ l :=
  ReachableFrom.mono h hr

/-- Reachability only ever depends on `µ` through the bindings at
    reachable locations: if two stores agree on all locations reachable
    from a common root set, the *same* locations are reachable from those
    roots in both stores.  This is the basic "locality" fact underlying
    the whole development.

    到達可能性は「到達可能な location での束縛」だけに依存する：
    2つのストアが、共通の根の集合から到達可能な location すべてで
    値が一致しているなら、その根から到達可能な location の集合自体も
    両方のストアで完全に同じになる。これは今回の証明全体を支える
    基本的な「局所性 (locality)」の事実。 -/
theorem ReachableFrom.agree {roots : List Nat} {μ1 μ2 : Store}
    (hagree : ∀ l, ReachableFrom roots μ1 l → lookupOpt μ1 l = lookupOpt μ2 l)
    {l : Nat} (hr : ReachableFrom roots μ1 l) : ReachableFrom roots μ2 l := by
  induction hr with
  | base hl => exact .base hl
  | @step l l' hprev hl' ih =>
      -- hprev（μ1側で到達可能）に hagree を適用して、μ1とμ2での値が
      -- 一致することを取り出し、それを使って locOf の中身を μ2 側に付け替える
      have heq : lookupOpt μ1 l = lookupOpt μ2 l := hagree l hprev
      apply ReachableFrom.step ih
      unfold locOf at hl' ⊢
      rw [← heq]
      exact hl'

/- ============================================================ -/
/-  The garbage-collection step                                   -/
/-  ガベージコレクション（GC）のステップ                            -/
/- ============================================================ -/

/-- `GCStep t μ μ'` says `μ'` is exactly `µ` restricted to
    `reachable(t, µ)`, i.e. this is precisely rule (E-GC) from the printed
    solution: "µ′ is the restriction of µ to reachable(t, µ)".

    `GCStep t μ μ'` は、`μ'` がちょうど `µ` を `reachable(t, µ)` に
    制限したものであることを表す——つまり模範解答の規則 (E-GC) そのもの：
    「µ′ は µ を reachable(t, µ) に制限したものである」。
    1つ目の条件が「定義域は "µ にもあり、かつ到達可能" な location だけ」、
    2つ目の条件が「残した部分の値は µ と完全に一致（変更しない）」を表す。 -/
def GCStep (t : Term) (μ μ' : Store) : Prop :=
  (∀ l, l ∈ dom μ' ↔ (l ∈ dom μ ∧ Reachable t μ l)) ∧
  (∀ l, l ∈ dom μ' → lookupOpt μ' l = lookupOpt μ l)

/- ============================================================ -/
/-  Ordinary (non-GC) evaluation                                  -/
/-  通常の（GCを含まない）評価                                     -/
/- ============================================================ -/

/-- The call-by-value, left-to-right small-step semantics for
    `FullUntypedRef`'s core (TAPL Fig. 13.1): E-AppAbs, E-App1, E-App2,
    E-RefV, E-Ref, E-DerefLoc, E-Deref, E-Assign (both the "location"
    version and the two congruence versions).  We use ordinary structural
    (congruence) rules instead of TAPL's "evaluation context" formulation;
    the two styles define the same relation, and congruence rules are the
    much more convenient shape for a mechanized proof by induction on
    derivations.

    Configurations here carry, besides the term and the store, an
    allocation counter `n : Nat`: `ref v` always allocates at location
    `n` and bumps the counter to `n+1`.  This is *not* extra content of
    the language (any convention for choosing a fresh location is
    semantically equivalent); it is a bookkeeping device that lets us
    later compare a "fully evaluated" run against a "garbage-collected"
    run of the *same* program and be sure that both allocate at exactly
    the same physical locations, so that the two runs really do produce
    the identical term `t'` demanded by the theorem below.  (Without
    this device — e.g. if `ref` could allocate at an arbitrary location
    not currently in the domain of its own store — a location freed by
    garbage collection could later be legitimately re-used by the
    collected run while the uncollected run, which never freed it,
    would have to allocate elsewhere, and the two runs would then
    diverge on freshly-allocated locations for reasons that have
    nothing to do with the correctness of collection.  Monotonic
    allocation is how real implementations avoid exactly this
    non-issue.)

    `FullUntypedRef` の中核部分（TAPL 図13.1）に対する、
    call-by-value・左から右へのスモールステップ意味論：
    E-AppAbs, E-App1, E-App2, E-RefV, E-Ref, E-DerefLoc, E-Deref,
    E-Assign（「location」版と2つの合同規則版）。
    TAPL の「評価文脈 (evaluation context)」による定式化ではなく、
    普通の構造的（合同）規則を使っている——両者は同じ関係を定義するが、
    合同規則の形の方が、導出に関する帰納法による機械的証明にずっと
    向いている。

    ここでの「実行時の状態（configuration）」は、項とストアに加えて
    割り当てカウンタ `n : Nat` を持つ：`ref v` は必ず location `n` に
    割り当て、カウンタを `n+1` に進める。これは言語自体の「余分な情報」
    ではない（新しい location をどう選ぶかは、意味論的にはどんな流儀を
    採っても同値）。これは後で「完全に評価した実行」と「同じプログラムの
    GC付き実行」を比較する際に、両者が *物理的に全く同じ location* に
    割り当てることを保証するための帳簿づけの道具である。これにより、
    後述の定理が要求する「両者が同一の項 `t'` に到達する」ことが
    成り立つ。
    （もしこの仕組みがなく、たとえば `ref` が「現在の自分のストアの
    定義域に入っていない任意の location」に割り当ててよいことにすると：
    GCで解放された location を、GC付きの実行では正当に再利用できて
    しまう一方、GCなしの実行ではその location を一度も解放していない
    ので別の場所に割り当てざるを得ず、GCの正しさとは無関係な理由で
    新規割り当ての location が食い違ってしまう。単調な割り当ては、
    実際の実装がこの「問題ですらない問題」を避けている方法そのもの
    である。） -/
inductive Step : Term → Nat → Store → Term → Nat → Store → Prop where
  | appAbs {t v n μ} : IsValue v → Step (app (abs t) v) n μ (substTop v t) n μ
      -- E-AppAbs：β簡約。ストアも n も変化しない
  | app1 {t1 t1' t2 n n' μ μ'} :
      Step t1 n μ t1' n' μ' → Step (app t1 t2) n μ (app t1' t2) n' μ'
      -- E-App1：関数側を先に評価する合同規則
  | app2 {v1 t2 t2' n n' μ μ'} :
      IsValue v1 → Step t2 n μ t2' n' μ' → Step (app v1 t2) n μ (app v1 t2') n' μ'
      -- E-App2：関数が値になったら引数側を評価する合同規則
  | refV {v n μ} : IsValue v → n ∉ dom μ →
      Step (ref v) n μ (loc n) (n + 1) (alloc μ n v)
      -- E-RefV：新規割り当て。必ずカウンタ n の場所に確保し、n を進める
  | ref1 {t t' n n' μ μ'} : Step t n μ t' n' μ' → Step (ref t) n μ (ref t') n' μ'
      -- E-Ref：ref の中身を評価する合同規則
  | derefLoc {n μ l v} : lookupOpt μ l = some v → Step (deref (loc l)) n μ v n μ
      -- E-DerefLoc：参照の中身を読む（ストア・n は変化しない）
  | deref1 {t t' n n' μ μ'} : Step t n μ t' n' μ' → Step (deref t) n μ (deref t') n' μ'
      -- E-Deref：deref の中身を評価する合同規則
  | assignLoc {n μ l v} : IsValue v → l ∈ dom μ →
      Step (assign (loc l) v) n μ unit n (update μ l v)
      -- E-Assign（location版）：既存の location に値を書き込む
  | assign1 {t1 t1' t2 n n' μ μ'} :
      Step t1 n μ t1' n' μ' → Step (assign t1 t2) n μ (assign t1' t2) n' μ'
      -- E-Assign1：代入の左辺（location 側）を評価する合同規則
  | assign2 {v1 t2 t2' n n' μ μ'} : IsValue v1 → Step t2 n μ t2' n' μ' →
      Step (assign v1 t2) n μ (assign v1 t2') n' μ'
      -- E-Assign2：代入の右辺（書き込む値）を評価する合同規則

/-- Reflexive-transitive closure of `Step`, i.e. `→*`.
    `Step` の反射推移閉包、すなわち `→*`（何度でも通常のステップを
    踏める、という関係）。`refl`（0回）と `tail`（末尾に1回追加）の
    2つのコンストラクタで定義する、よくあるスタイル。 -/
inductive StepStar : Term → Nat → Store → Term → Nat → Store → Prop where
  | refl {t n μ} : StepStar t n μ t n μ
  | tail {t n μ t' n' μ' t'' n'' μ''} :
      StepStar t n μ t' n' μ' → Step t' n' μ' t'' n'' μ'' → StepStar t n μ t'' n'' μ''

-- 1回のステップは（当然）0回以上のステップの特別な場合
theorem StepStar.single {t n μ t' n' μ'} (h : Step t n μ t' n' μ') :
    StepStar t n μ t' n' μ' := StepStar.tail StepStar.refl h

-- StepStar は連結できる（推移律）
theorem StepStar.trans {t1 n1 μ1 t2 n2 μ2 t3 n3 μ3}
    (h1 : StepStar t1 n1 μ1 t2 n2 μ2) (h2 : StepStar t2 n2 μ2 t3 n3 μ3) :
    StepStar t1 n1 μ1 t3 n3 μ3 := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact StepStar.tail ih hstep

/- ============================================================ -/
/-  Structural ("locality") lemmas about `Step`                   -/
/-  `Step` に関する構造的な（「局所性」の）補題たち                 -/
/- ============================================================ -/
/-
   These three lemmas make precise the sense in which a single evaluation
   step can only ever touch bindings that are *currently named* in the
   term being evaluated:

     (A) the domain of the store never shrinks;
     (B) any location that is newly added to the store during the step
         literally occurs in the resulting term (this is how a fresh
         allocation becomes "visible": `ref v --> l`);
     (C) any location whose *value* actually changes during the step
         (and which was already present beforehand) literally occurs in
         the term *before* the step (this is how `assignLoc` shows up:
         you have to be holding `loc l` to write through it).

   Together these say precisely that `Step` cannot reach outside the set
   of locations mentioned in the term it is evaluating — exactly the
   locality property that licenses garbage collection.

   以下の3つの補題は、「1回の評価ステップは、評価中の項に
   "現在まさに名前が書かれている" 束縛しか触れない」ということを
   厳密に述べたもの：

   (A) ストアの定義域は決して縮まない
   (B) ステップの途中でストアに新しく追加される location は、
       文字どおり評価結果の項の中に出現する
       （新規割り当てが `ref v --> l` として「見える」仕組みそのもの）
   (C) ステップ中で実際に *値* が変わる location（もともと存在していた
       もの）は、文字どおりステップ *前* の項の中に出現する
       （`assignLoc` の本質：書き込むには `loc l` を手にしている
       必要がある）

   これらを合わせると、`Step` は評価中の項に書かれている location の
   集合の外には決して手を出さない、ということが言える——これこそが
   ガベージコレクションを正当化する「局所性」の性質。
-/

-- (A) ストアの定義域は単調に増加する（減ることはない）
theorem Step.dom_mono {t n μ t' n' μ'} (h : Step t n μ t' n' μ') :
    LSub (dom μ) (dom μ') := by
  induction h with
  | appAbs _ => exact LSub.refl _
  | app1 _ ih => exact ih
  | app2 _ _ ih => exact ih
  | refV _ _ => exact LSub_dom_alloc _ _ _
  | ref1 _ ih => exact ih
  | derefLoc _ => exact LSub.refl _
  | deref1 _ ih => exact ih
  | assignLoc _ _ => rw [dom_update]; exact LSub.refl _  -- 書き込みは定義域を変えない
  | assign1 _ ih => exact ih
  | assign2 _ _ ih => exact ih

-- (B) 新しく増えた location は、必ず評価後の項の中に出現する
theorem Step.new_loc_in_result {t n μ t' n' μ'} (h : Step t n μ t' n' μ') :
    ∀ l, l ∈ dom μ' → l ∉ dom μ → l ∈ locations t' := by
  induction h with
  | appAbs _ => intro l hl' hl; exact absurd hl' hl  -- ストア不変なので新規追加はあり得ない
  | app1 _ ih =>
      intro l hl' hl
      exact List.mem_append.mpr (Or.inl (ih l hl' hl))
  | app2 _ _ ih =>
      intro l hl' hl
      exact List.mem_append.mpr (Or.inr (ih l hl' hl))
  | @refV v n0 μ0 _ hfresh =>
      -- 新しい location は l = n0（今回割り当てた場所）しかあり得ない。
      -- そして評価結果はちょうど `loc n0` なので、確かにそこに出現する
      intro l hl' hl
      have := (mem_dom_alloc μ0 n0 l v).mp hl'
      rcases this with h1 | h1
      · exact absurd h1 hl
      · subst h1; simp [locations]
  | ref1 _ ih =>
      intro l hl' hl
      simpa [locations] using ih l hl' hl
  | derefLoc _ => intro l hl' hl; exact absurd hl' hl
  | deref1 _ ih =>
      intro l hl' hl
      simpa [locations] using ih l hl' hl
  | assignLoc _ _ =>
      -- update は定義域を変えないので、新規追加はあり得ない
      intro l hl' hl
      rw [mem_dom_update] at hl'
      exact absurd hl' hl
  | assign1 _ ih =>
      intro l hl' hl
      exact List.mem_append.mpr (Or.inl (ih l hl' hl))
  | assign2 _ _ ih =>
      intro l hl' hl
      exact List.mem_append.mpr (Or.inr (ih l hl' hl))

-- (C) 値が実際に変わった location は、必ず評価前の項の中に出現する
theorem Step.changed_loc_in_source {t n μ t' n' μ'} (h : Step t n μ t' n' μ') :
    ∀ l, l ∈ dom μ → lookupOpt μ l ≠ lookupOpt μ' l → l ∈ locations t := by
  induction h with
  | appAbs _ => intro l _ hne; exact absurd rfl hne  -- ストア不変なので「変化」自体があり得ない
  | app1 _ ih =>
      intro l hl hne
      exact List.mem_append.mpr (Or.inl (ih l hl hne))
  | app2 _ _ ih =>
      intro l hl hne
      exact List.mem_append.mpr (Or.inr (ih l hl hne))
  | @refV v n0 μ0 _ hfresh =>
      -- 新規割り当ては既存の location の値を書き換えない（alloc は追記のみ）
      intro l hl hne
      have hne_ll0 : l ≠ n0 := fun he => hfresh (he ▸ hl)
      exact absurd (lookup_alloc_other μ0 n0 l v hne_ll0).symm hne
  | ref1 _ ih =>
      intro l hl hne
      simpa [locations] using ih l hl hne
  | derefLoc _ => intro l _ hne; exact absurd rfl hne
  | deref1 _ ih =>
      intro l hl hne
      simpa [locations] using ih l hl hne
  | @assignLoc n0 μ0 l0 v _ _ =>
      -- l = l0（実際に書き込んだ場所）なら loc l0 が項の中に出現、
      -- l ≠ l0 なら値は変わっていないはずなので矛盾
      intro l hl hne
      by_cases heq : l = l0
      · subst heq; simp [locations]
      · exact absurd (lookup_update_other μ0 l0 l v heq).symm hne
  | assign1 _ ih =>
      intro l hl hne
      exact List.mem_append.mpr (Or.inl (ih l hl hne))
  | assign2 _ _ ih =>
      intro l hl hne
      exact List.mem_append.mpr (Or.inr (ih l hl hne))

/- ============================================================ -/
/-  Boundedness of the allocation counter                         -/
/-  割り当てカウンタによる「有界性」                                -/
/- ============================================================ -/

/-- `Bounded n μ` says every location currently in the store is `< n`:
    i.e. `n` (and everything above it) is available for fresh
    allocation.  `Step` maintains this invariant, and — crucially — the
    counter `n` only ever increases, so a location once used is *never*
    reused, even if garbage collection later frees it.

    `Bounded n μ` は、現在ストアに入っているすべての location が `n`
    未満であることを表す。つまり `n`（とそれ以上の数）は、まだ新規割り当てに
    使っていない、ということ。`Step` はこの不変条件を保存し、
    ——ここが肝心なところだが——カウンタ `n` は単調に増加するだけなので、
    一度使われた location は、たとえ後でGCによって解放されても
    *決して* 再利用されない。 -/
def Bounded (n : Nat) (μ : Store) : Prop := ∀ l, l ∈ dom μ → l < n

-- Bounded なら、カウンタ n 自体はまだストアに入っていない（＝新規割り当て可能）
theorem Bounded.mono {n μ} (h : Bounded n μ) : n ∉ dom μ := fun hmem => Nat.lt_irrefl n (h n hmem)

-- カウンタが大きくなる分には Bounded は保たれる
theorem Bounded.weaken {n n' μ} (h : Bounded n μ) (hle : n ≤ n') : Bounded n' μ :=
  fun l hl => Nat.lt_of_lt_of_le (h l hl) hle

-- 定義域が縮む分（部分集合になる分）には Bounded は保たれる
theorem Bounded.subset {n μ μ'} (h : Bounded n μ) (hsub : LSub (dom μ') (dom μ)) :
    Bounded n μ' := fun l hl => h l (hsub l hl)

-- Step を1回踏んでも：カウンタは（弱く）増加するだけで、Bounded は新しいカウンタで保たれる
theorem Step.preserves_bounded {t n μ t' n' μ'} (h : Step t n μ t' n' μ')
    (hb : Bounded n μ) : n ≤ n' ∧ Bounded n' μ' := by
  induction h with
  | appAbs _ => exact ⟨Nat.le_refl _, hb⟩
  | @app1 t1 t1' t2 n n' μ μ' _ ih => exact ih hb
  | @app2 v1 t2 t2' n n' μ μ' _ _ ih => exact ih hb
  | @refV v n0 μ0 _ hfresh =>
      -- 新規割り当て：カウンタは n0+1 に、既存の束縛は n0 < n0+1、
      -- 新しい束縛（location = n0）も n0 < n0+1 で Bounded を満たす
      refine ⟨Nat.le_succ _, ?_⟩
      intro l hl
      rw [mem_dom_alloc] at hl
      rcases hl with hl | hl
      · exact Nat.lt_succ_of_lt (hb l hl)
      · subst hl; exact Nat.lt_succ_self _
  | @ref1 t t' n n' μ μ' _ ih => exact ih hb
  | derefLoc _ => exact ⟨Nat.le_refl _, hb⟩
  | @deref1 t t' n n' μ μ' _ ih => exact ih hb
  | @assignLoc n0 μ0 l0 v _ _ =>
      -- 書き込みは定義域を変えないので Bounded はそのまま成り立つ
      refine ⟨Nat.le_refl _, ?_⟩
      intro l hl
      rw [mem_dom_update] at hl
      exact hb l hl
  | @assign1 t1 t1' t2 n n' μ μ' _ ih => exact ih hb
  | @assign2 v1 t2 t2' n n' μ μ' _ _ ih => exact ih hb

-- 何回ステップを踏んでも同じことが成り立つ（preserves_bounded を StepStar 上に拡張）
theorem StepStar.preserves_bounded {t n μ t' n' μ'} (h : StepStar t n μ t' n' μ')
    (hb : Bounded n μ) : n ≤ n' ∧ Bounded n' μ' := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, hb⟩
  | tail _ hstep ih =>
      obtain ⟨hle, hb'⟩ := ih
      obtain ⟨hle2, hb''⟩ := hstep.preserves_bounded hb'
      exact ⟨Nat.le_trans hle hle2, hb''⟩

/- ============================================================ -/
/-  The "Safe" relation: `B` is a safe (possibly partially or     -/
/-  fully garbage-collected) version of `A` relative to `t`        -/
/-  「Safe」関係：`B` は、項 `t` に対して `A` の                    -/
/-  「安全な（部分的または完全に GC 済みの）版」であることを表す     -/
/- ============================================================ -/

-- 単なる ++ の可換性（メンバーシップの意味で）。局所的に何度も使う小道具
theorem LSub_append_comm (l1 l2 : List Nat) : LSub (l1 ++ l2) (l2 ++ l1) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append.mpr (Or.inr h)
  · exact List.mem_append.mpr (Or.inl h)

/-- `Safe t n A B` says: `A` is a store bounded by the counter `n`;
    `B`'s domain is contained in `A`'s; `B` already contains every
    location directly named by `t` (so, in particular, `t` can run
    against `B` just as well as against `A`); `B` is *self-closed*
    (chasing pointers starting from any binding in `B` never leaves
    `B`); and `B` agrees with `A` on every location it does contain.

    This is exactly the shape of the guarantee we need to relate a
    plain run against `A` to a garbage-collected run against `B`: `B`
    is "big enough" to run `t` and to keep running afterwards (because
    it's self-closed), while possibly omitting bindings of `A` that are
    (already, or eventually provably) irrelevant to `t`.

    `GCStep t A B` (the *exact* one-shot restriction to `reachable(t,A)`
    from the printed solution) is the extremal/smallest instance of
    `Safe t n A B`; but `Safe` also includes every intermediate/partial
    collection, and — importantly — the "no collection at all" instance
    `B = A`.  This extra flexibility is exactly what makes `Safe`
    preserved by ordinary evaluation steps on *either* side, which is
    the crux of the whole argument.

    `Safe t n A B` は次のことを表す：
    ・`A` はカウンタ `n` で有界なストア（`Bounded n A`）
    ・`B` の定義域は `A` の定義域に含まれる（`B` は `A` の一部）
    ・`B` はすでに `t` が直接名指ししている location をすべて含んでいる
      （したがって特に、`t` は `A` に対してと同様に `B` に対しても実行できる）
    ・`B` は「自己閉包」している（`B` 内のどの束縛から出発してポインタを
      辿っても、決して `B` の外に出ない）
    ・`B` は自分が含んでいる location については `A` と値が一致する

    これはまさに、「`A` に対する素の実行」と「`B` に対する GC 付き実行」を
    結び付けるために必要な保証の形になっている：`B` は `t` を実行するのに
    十分な大きさがあり（自己閉包しているので）その後も実行を続けられる、
    それでいて `t` に無関係な `A` の束縛は（すでに、あるいはいずれ証明可能に）
    省略していてよい。

    模範解答の `GCStep t A B`（`reachable(t,A)` へのちょうど1回きりの
    厳密な制限）は、`Safe t n A B` の「極端な・最小の」場合に過ぎない。
    `Safe` はそれ以外の「途中までしか GC していない」あらゆる状態、
    そして重要なことに「GC を一切していない」場合（`B = A`）も含む。
    この余分な柔軟性こそが、`Safe` が *どちら側* の通常の評価ステップに
    対しても保存される、という今回の議論全体の核心を支えている。 -/
def Safe (t : Term) (n : Nat) (A B : Store) : Prop :=
  Bounded n A ∧                                                     -- (1) A は n で有界
  LSub (dom B) (dom A) ∧                                            -- (2) B ⊆ A（定義域として）
  LSub (locations t) (dom B) ∧                                      -- (3) B は t の根を覆っている
  (∀ l, l ∈ dom B → ∀ l', l' ∈ locOf B l → l' ∈ dom B) ∧            -- (4) B は自己閉包
  (∀ l, l ∈ dom B → lookupOpt B l = lookupOpt A l)                  -- (5) B は A と一致（共通部分で）

-- 以下は Safe の5条件をそれぞれ取り出すための射影（アクセサ）
theorem Safe.bounded {t n A B} (h : Safe t n A B) : Bounded n A := h.1
theorem Safe.dom_sub {t n A B} (h : Safe t n A B) : LSub (dom B) (dom A) := h.2.1
theorem Safe.roots_covered {t n A B} (h : Safe t n A B) : LSub (locations t) (dom B) := h.2.2.1
theorem Safe.self_closed {t n A B} (h : Safe t n A B) :
    ∀ l, l ∈ dom B → ∀ l', l' ∈ locOf B l → l' ∈ dom B := h.2.2.2.1
theorem Safe.agree {t n A B} (h : Safe t n A B) :
    ∀ l, l ∈ dom B → lookupOpt B l = lookupOpt A l := h.2.2.2.2

/-- Every location reachable from `t` in the *safe* store `B` is
    already inside `dom B` — this is the derived, "global" reachability
    consequence of the two local conditions `roots_covered` and
    `self_closed`.

    「安全な」ストア `B` において `t` から到達可能な location は、
    すでにすべて `dom B` に入っている——これは局所的な2つの条件
    （`roots_covered` と `self_closed`）から導かれる「大域的な」
    到達可能性の帰結。`roots_covered`（根を覆う）＋`self_closed`
    （自己閉包）＝「推移閉包全体を覆う」という、まさに前回の質問で
    説明した「到達可能性は base と step の帰納的閉包である」ことの
    言い換え。 -/
theorem Safe.reachable_in_dom {t n A B} (h : Safe t n A B) :
    ∀ l, Reachable t B l → l ∈ dom B := by
  intro l hr
  induction hr with
  | base hl => exact h.roots_covered _ hl
  | step hprev hl' ih => exact h.self_closed _ ih _ hl'

/-- Shrinking the term (i.e. only asking `Safe` to cover a *sub*set of
    the original term's locations) is always harmless: everything else
    about `Safe` is entirely term-independent.

    項を「縮める」（＝もとの項の locations の部分集合しか覆っていない
    ことしか要求しない）方向への言い換えは、常に問題なく行える：
    `Safe` の条件(3)以外はすべて項に依存しないので、そのまま流用できる。
    これが `Safe.lift`／`Safe.down` の合同規則のケース（app1 など）で
    「部分項についての Safe」を取り出すために使う道具。 -/
theorem Safe.reindex {t1 t2 n A B} (hsub : LSub (locations t2) (locations t1))
    (h : Safe t1 n A B) : Safe t2 n A B :=
  ⟨h.bounded, h.dom_sub, fun l hl => h.roots_covered _ (hsub l hl), h.self_closed, h.agree⟩

-- 反射律：A 自身は自明に「A に対して安全」（GC を一切していない、という状態）
theorem Safe.refl {t n A} (hb : Bounded n A) (hroots : LSub (locations t) (dom A))
    (hclosed : ∀ l, l ∈ dom A → ∀ l', l' ∈ locOf A l → l' ∈ dom A) : Safe t n A A :=
  ⟨hb, LSub.refl _, hroots, hclosed, fun _ _ => rfl⟩

/-- Absorbing an (E-GC) step on the safe side: collecting further never
    breaks `Safe`.

    安全な側（B）でさらに (E-GC) ステップを1回行っても、`Safe` は
    壊れない——つまり「もっと集める」ことは常に安全。
    `GCStep` は `Reachable t B` へのちょうどの制限なので、条件(3)(4)(5)を
    それぞれ、到達可能性の base/step 構造とうまく噛み合わせて示す。 -/
theorem Safe.gc_absorb {t n A B C} (h : Safe t n A B) (hgc : GCStep t B C) :
    Safe t n A C := by
  have hreachB : ∀ l, Reachable t B l → l ∈ dom B := h.reachable_in_dom
  refine ⟨h.bounded, ?_, ?_, ?_, ?_⟩
  · -- dom C ⊆ dom A：C ⊆ B（GCStepの定義）⊆ A（hの条件2）
    intro l hl
    have := (hgc.1 l).mp hl
    exact h.dom_sub _ this.1
  · -- locations t ⊆ dom C：t の根はもともと B に含まれ（roots_covered）、
    -- かつ base により到達可能なので、GCStep の定義から C にも残る
    intro l hl
    have h1 : l ∈ dom B := h.roots_covered _ hl
    have h2 : Reachable t B l := ReachableFrom.base hl
    exact (hgc.1 l).mpr ⟨h1, h2⟩
  · -- C self-closed：C の中の l から1歩進んだ l' は、B の中でも
    -- （到達可能性の step により）到達可能であり続けるので、
    -- GCStep の定義により l' も C に残る
    intro l hl l' hl'
    have hlB : l ∈ dom B := ((hgc.1 l).mp hl).1
    have hrl : Reachable t B l := ((hgc.1 l).mp hl).2
    have hlookup : lookupOpt C l = lookupOpt B l := hgc.2 l hl
    have hl'B : l' ∈ locOf B l := by
      unfold locOf at hl' ⊢
      rw [hlookup] at hl'
      exact hl'
    have hrl' : Reachable t B l' := ReachableFrom.step hrl hl'B
    have hl'B' : l' ∈ dom B := hreachB _ hrl'
    exact (hgc.1 l').mpr ⟨hl'B', hrl'⟩
  · -- C agrees with A：C は B の部分集合で B と値が一致し（GCStepの定義）、
    -- B は A と値が一致する（hの条件5）ので、推移的に C も A と一致
    intro l hl
    have hlB : l ∈ dom B := ((hgc.1 l).mp hl).1
    rw [hgc.2 l hl, h.agree l hlB]


/- ============================================================ -/
/-  The two commutation ("Up"/"Down") lemmas                      -/
/-  2つの「入れ替え」（"Up"／"Down"）補題                          -/
/- ============================================================ -/

/-- **"Up" / lifting lemma.**  If the *safe* (already partly
    garbage-collected) store `B` can take an ordinary step, then the
    *big* store `A` (of which `B` is a safe sub-store) can take the
    *identical* step (same term, same allocation counter), landing in a
    configuration that is again related by `Safe`.  This is what lets us
    replay a garbage-collected run as an ordinary (uncollected) run: see
    the header comment for why the shared allocation counter is what
    makes "the identical step" meaningful.

    **"Up"（持ち上げ）補題。** 「安全な」（すでに部分的にGC済みの）
    ストア `B` が通常のステップを1回踏めるなら、`B` の（安全な）親である
    「大きな」ストア `A` も *全く同じ* ステップ（同じ項・同じ割り当て
    カウンタ）を踏むことができ、その結果もまた `Safe` の関係を満たす。
    これによって「GC付きの実行」を「通常の（GCなしの）実行」として
    再現できる——ヘッダーコメントで説明したとおり、割り当てカウンタを
    共有していることが「全く同じステップ」という言明を意味あるものに
    している。

    合同規則のケース（app1 など）では、「部分項について Safe を
    縮小 (`Safe.reindex`) → 帰納法の仮定を適用 → 結果を元の項に
    戻す」という流れで進む。ここで重要な簡略化は、`Safe` の
    条件(1)(2)(4)(5)がすべて「項に依存しない」ことで、部分項について
    証明したものをそのまま流用できる点——手を動かす必要があるのは
    条件(3)（根の被覆）だけであり、それも単なるリストの `++` の
    議論で済む（もう一方の部分項（app1 なら t2）の根は、もともとの
    Safe から取り出し、`Step.dom_mono` で定義域が増える方向に運ぶだけ）。

    `appAbs`／`refV`／`derefLoc`／`assignLoc` の各「基本」規則の
    ケースでは、`Bounded`、`mem_dom_alloc`／`dom_update`、
    `lookup_alloc_same`／`other`、`lookup_update_same`／`other`、
    `locations_substTop`、`LSub_append_comm` だけを使えば証明できる。 -/
theorem Safe.lift {t n B t' n' C} (hstep : Step t n B t' n' C) :
    ∀ A, Safe t n A B → ∃ A', Step t n A t' n' A' ∧ Safe t' n' A' C := by
  -- Step の導出（hstep）に関する構造的帰納法。合同規則のケースでは
  -- Safe.reindex で部分項に絞り込んでから帰納法の仮定 ih を適用し、
  -- 基本規則（appAbs / refV / derefLoc / assignLoc）のケースでは
  -- Safe の5条件を1つずつ手で確認する。
  induction hstep with
  | @appAbs t0 v n μ hv =>
      -- E-AppAbs：β簡約。ストアは変化しない（A'=A）。
      -- locations(substTop v t0) ⊆ locations v ++ locations t0
      --   = locations t0 ++ locations v（並び替え）= locations(app(abs t0)v)
      -- なので、reindex で元の Safe をそのまま使い回せる
      intro A hSafe
      refine ⟨A, Step.appAbs hv, ?_⟩
      apply Safe.reindex (t1 := app (abs t0) v) ?_ hSafe
      intro x hx
      have h1 := locations_substTop v t0 x hx
      exact LSub_append_comm _ _ x h1
  | @app1 t1 t1' t2 n n' μ μ' hsub ih =>
      -- E-App1：t1 側を評価する合同規則。
      -- t1 についての Safe を取り出して ih を適用し、A' を得る。
      -- 条件(1)(2)(4)(5)は t1' についての Safe からそのまま流用できる
      -- （項に依存しないため）。条件(3)だけは t2 の分も追加で必要になるが、
      -- それは「もとの Safe から locations t2 ⊆ dom μ を取り出し、
      -- Step.dom_mono で dom μ ⊆ dom μ' へ運ぶ」だけで済む
      -- （t2 自体は変化していないので、これで十分）。
      intro A hSafe
      have hSafe1 : Safe t1 n A μ := Safe.reindex (LSub.appendLeft _ _) hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe1
      refine ⟨A', Step.app1 hstepA, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have ht2 : LSub (locations t2) (dom μ) := by
        intro x hx; exact hSafe.roots_covered x (List.mem_append.mpr (Or.inr hx))
      have ht2' : LSub (locations t2) (dom μ') := LSub.trans ht2 (Step.dom_mono hsub)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hSafe'.roots_covered x h
      · exact ht2' x h
  | @app2 v1 t2 t2' n n' μ μ' hv1 hsub ih =>
      -- E-App2：t2 側を評価する合同規則（app1 と対称、v1 側が「変化しない方」）
      intro A hSafe
      have hSafe1 : Safe t2 n A μ := Safe.reindex (LSub.appendRight _ _) hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe1
      refine ⟨A', Step.app2 hv1 hstepA, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have hv1' : LSub (locations v1) (dom μ) := by
        intro x hx; exact hSafe.roots_covered x (List.mem_append.mpr (Or.inl hx))
      have hv1'' : LSub (locations v1) (dom μ') := LSub.trans hv1' (Step.dom_mono hsub)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hv1'' x h
      · exact hSafe'.roots_covered x h
  | @refV v n0 μ hv hfresh =>
      -- E-RefV：新規割り当て。μ（=B）側では n0 ∉ dom μ が与えられている
      -- （hfresh）。A 側で n0 が新規割り当て可能であること（n0 ∉ dom A）は、
      -- hSafe.bounded（Bounded n0 A）から Bounded.mono で直接得られる
      -- ——ここがまさに「共有カウンタ」の仕組みが効いている箇所：
      -- B 側と A 側で「同じ n0」に割り当てられることが保証される。
      intro A hSafe
      have hnA : n0 ∉ dom A := hSafe.bounded.mono
      refine ⟨alloc A n0 v, Step.refV hv hnA, ?_, ?_, ?_, ?_, ?_⟩
      · -- (1) Bounded (n0+1) (alloc A n0 v)：既存分は n0<n0+1、新規分も n0<n0+1
        intro l hl
        rw [mem_dom_alloc] at hl
        rcases hl with hl | hl
        · exact Nat.lt_succ_of_lt (hSafe.bounded l hl)
        · subst hl; exact Nat.lt_succ_self _
      · -- (2) dom(alloc μ n0 v) ⊆ dom(alloc A n0 v)
        intro l hl
        rw [mem_dom_alloc] at hl ⊢
        rcases hl with hl | hl
        · exact Or.inl (hSafe.dom_sub l hl)
        · exact Or.inr hl
      · -- (3) locations(loc n0) = [n0] ⊆ dom(alloc μ n0 v)：n0 自身は今まさに追加した場所
        intro l hl
        simp only [locations, List.mem_singleton] at hl
        exact (mem_dom_alloc _ _ _ _).mpr (Or.inr hl)
      · -- (4) alloc μ n0 v の自己閉包：既存の l なら旧 μ の自己閉包を、
        --     新規の l=n0 なら「v の locations はもともとの Safe の
        --     条件(3)（locations(ref v) = locations v ⊆ dom μ）」を使う
        intro l hl l' hl'
        rw [mem_dom_alloc] at hl
        rcases hl with hl | hl
        · have hlne : l ≠ n0 := fun he => hfresh (he ▸ hl)
          have heq : locOf (alloc μ n0 v) l = locOf μ l := by
            unfold locOf; rw [lookup_alloc_other _ _ _ _ hlne]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.self_closed l hl l' hl'))
        · have heq : locOf (alloc μ n0 v) l = locations v := by
            rw [hl]; unfold locOf; rw [lookup_alloc_same _ _ _ hfresh]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.roots_covered l' hl'))
      · -- (5) alloc μ n0 v は alloc A n0 v と一致：既存分は旧 agree を、
        --     新規分（l=n0）は両方とも同じ v が入るのでそのまま一致
        intro l hl
        rw [mem_dom_alloc] at hl
        rcases hl with hl | hl
        · have hlne : l ≠ n0 := fun he => hfresh (he ▸ hl)
          rw [lookup_alloc_other _ _ _ _ hlne, hSafe.agree l hl, lookup_alloc_other _ _ _ _ hlne]
        · subst hl
          rw [lookup_alloc_same _ _ _ hfresh, lookup_alloc_same _ _ _ hnA]
  | @ref1 t0 t0' n n' μ μ' hsub ih =>
      -- E-Ref：ref の中身を評価する合同規則。
      -- locations(ref t0) = locations t0 が定義上「等式」で成り立つので、
      -- Safe (ref t0) n A μ は定義上そのまま Safe t0 n A μ と同じ
      -- （reindex すら不要、ただの型合わせ）
      intro A hSafe
      have hSafe0 : Safe t0 n A μ := hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe0
      exact ⟨A', Step.ref1 hstepA, hSafe'⟩
  | @derefLoc n μ l0 v0 hlk =>
      -- E-DerefLoc：参照の中身を読む。ストアは変化しない（A'=A）。
      -- μ(=B) 側で l0 に v0 が入っている（hlk）ことと、l0 が Safe の
      -- 条件(3)から dom μ に入っていること、条件(5)の一致から、
      -- A 側でも l0 に同じ v0 が入っていることが分かり、同じ規則を A で発火できる。
      -- 続く Safe v0 n A μ の条件(3)（locations v0 ⊆ dom μ）は、
      -- ちょうど「B の自己閉包を l0 に適用したもの」そのもの。
      intro A hSafe
      have hl0 : l0 ∈ dom μ := hSafe.roots_covered l0 (by simp [locations])
      have hlkA : lookupOpt A l0 = some v0 := by rw [← hSafe.agree l0 hl0, hlk]
      refine ⟨A, Step.derefLoc hlkA, hSafe.bounded, hSafe.dom_sub, ?_, hSafe.self_closed, hSafe.agree⟩
      have hlocOf : locOf μ l0 = locations v0 := by unfold locOf; rw [hlk]
      intro x hx
      apply hSafe.self_closed l0 hl0
      rw [hlocOf]; exact hx
  | @deref1 t0 t0' n n' μ μ' hsub ih =>
      -- E-Deref：deref の中身を評価する合同規則（ref1 と同様、locations が等式で保たれる）
      intro A hSafe
      have hSafe0 : Safe t0 n A μ := hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe0
      exact ⟨A', Step.deref1 hstepA, hSafe'⟩
  | @assignLoc n0 μ l0 v0 hv0 hl0mem =>
      -- E-Assign（location版）：既存の場所への書き込み。
      -- l0 は Safe の条件(3)から dom μ に、条件(2)から dom A にも入っている。
      -- A 側でも同じ l0 に同じ v0 を書き込めばよい。
      intro A hSafe
      have hl0 : l0 ∈ dom μ := hSafe.roots_covered l0
        (by simp [locations])
      have hl0A : l0 ∈ dom A := hSafe.dom_sub l0 hl0
      have hv0sub : LSub (locations v0) (dom μ) := by
        intro x hx; exact hSafe.roots_covered x (by simp [locations]; exact Or.inr hx)
      refine ⟨update A l0 v0, Step.assignLoc hv0 hl0A, ?_, ?_, ?_, ?_, ?_⟩
      · -- (1) Bounded n0 (update A l0 v0)：update は定義域を変えない
        intro l hl; rw [dom_update] at hl; exact hSafe.bounded l hl
      · -- (2) dom(update μ l0 v0) ⊆ dom(update A l0 v0)：両辺とも update で定義域不変
        rw [dom_update, dom_update]; exact hSafe.dom_sub
      · -- (3) locations unit = []：代入の結果は unit なので自明
        intro x hx; cases hx
      · -- (4) update μ l0 v0 の自己閉包：l=l0 なら書き込んだ v0 の locations
        --     （もとの Safe の条件(3)から dom μ に含まれる）を使い、
        --     l≠l0 なら旧 μ の自己閉包をそのまま使う
        intro l hl l' hl'
        rw [dom_update] at hl ⊢
        by_cases heq : l = l0
        · rw [heq] at hl'
          have hlocOf : locOf (update μ l0 v0) l0 = locations v0 := by
            unfold locOf; rw [lookup_update_same _ _ _ hl0]
          rw [hlocOf] at hl'
          exact hv0sub l' hl'
        · have hlocOf : locOf (update μ l0 v0) l = locOf μ l := by
            unfold locOf; rw [lookup_update_other _ _ _ _ heq]
          rw [hlocOf] at hl'
          exact hSafe.self_closed l hl l' hl'
      · -- (5) update μ l0 v0 は update A l0 v0 と一致：
        --     l=l0 なら両方とも新しい v0、l≠l0 なら旧 agree をそのまま使う
        intro l hl
        rw [dom_update] at hl
        by_cases heq : l = l0
        · rw [heq, lookup_update_same _ _ _ hl0, lookup_update_same _ _ _ hl0A]
        · rw [lookup_update_other _ _ _ _ heq, hSafe.agree l hl, lookup_update_other _ _ _ _ heq]
  | @assign1 t1 t1' t2 n n' μ μ' hsub ih =>
      -- E-Assign1：代入の左辺（location 側）を評価する合同規則（app1 と同型）
      intro A hSafe
      have hSafe1 : Safe t1 n A μ := Safe.reindex (LSub.appendLeft _ _) hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe1
      refine ⟨A', Step.assign1 hstepA, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have ht2 : LSub (locations t2) (dom μ) := by
        intro x hx; exact hSafe.roots_covered x (List.mem_append.mpr (Or.inr hx))
      have ht2' : LSub (locations t2) (dom μ') := LSub.trans ht2 (Step.dom_mono hsub)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hSafe'.roots_covered x h
      · exact ht2' x h
  | @assign2 v1 t2 t2' n n' μ μ' hv1 hsub ih =>
      -- E-Assign2：代入の右辺（書き込む値）を評価する合同規則（app2 と同型）
      intro A hSafe
      have hSafe1 : Safe t2 n A μ := Safe.reindex (LSub.appendRight _ _) hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe1
      refine ⟨A', Step.assign2 hv1 hstepA, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have hv1' : LSub (locations v1) (dom μ) := by
        intro x hx; exact hSafe.roots_covered x (List.mem_append.mpr (Or.inl hx))
      have hv1'' : LSub (locations v1) (dom μ') := LSub.trans hv1' (Step.dom_mono hsub)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hv1'' x h
      · exact hSafe'.roots_covered x h


/-- **"Down" lemma.**  The mirror image of `Safe.lift`: if the *big*
    store `A` can take an ordinary step, then any safe sub-store `B` can
    take the identical step too, and the result is again `Safe`-related.
    Together with `Safe.lift` and `Safe.gc_absorb` this gives us
    everything needed to move freely between a plain evaluation and a
    garbage-collected one.

    **"Down"（引き下ろし）補題。** `Safe.lift` の鏡像：「大きな」
    ストア `A` が通常のステップを1回踏めるなら、その安全な部分ストア
    `B` も全く同じステップを踏むことができ、結果もまた `Safe` の関係を
    満たす。`Safe.lift`・`Safe.gc_absorb` と合わせて、これで
    「GCなしの実行」と「GC付きの実行」の間を自由に行き来するために
    必要な材料がすべて揃う。

    各ケースの構造は `Safe.lift` と全く対称。違うのは「どちら側の
    前提が最初から与えられていて、どちら側を導出するか」だけ：
    たとえば `refV` ケースでは、`Safe.lift` では B 側の
    `n0 ∉ dom μ` が与えられ A 側の `n0 ∉ dom A` を `Bounded` から
    導いたが、`Safe.down` では逆に A 側の `n0 ∉ dom A` が与えられ、
    B 側の `n0 ∉ dom B` を `dom_sub`（B ⊆ A）の対偶から導く。 -/
theorem Safe.down {t n A t' n' A'} (hstep : Step t n A t' n' A') :
    ∀ B, Safe t n A B → ∃ C, Step t n B t' n' C ∧ Safe t' n' A' C := by
  induction hstep with
  | @appAbs t0 v n μ hv =>
      -- Safe.lift の appAbs ケースと全く同じ論法（A と B の役割が
      -- 入れ替わっただけ）
      intro B hSafe
      refine ⟨B, Step.appAbs hv, ?_⟩
      apply Safe.reindex (t1 := app (abs t0) v) ?_ hSafe
      intro x hx
      have h1 := locations_substTop v t0 x hx
      exact LSub_append_comm _ _ x h1
  | @app1 t1 t1' t2 n n' μ μ' hsub ih =>
      -- Safe.lift の app1 ケースと同型（大小の役割が入れ替わっただけ）
      intro B hSafe
      have hSafe1 : Safe t1 n μ B := Safe.reindex (LSub.appendLeft _ _) hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B hSafe1
      refine ⟨C, Step.app1 hstepB, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have ht2 : LSub (locations t2) (dom B) := by
        intro x hx; exact hSafe.roots_covered x (List.mem_append.mpr (Or.inr hx))
      have ht2' : LSub (locations t2) (dom C) := LSub.trans ht2 (Step.dom_mono hstepB)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hSafe'.roots_covered x h
      · exact ht2' x h
  | @app2 v1 t2 t2' n n' μ μ' hv1 hsub ih =>
      intro B hSafe
      have hSafe1 : Safe t2 n μ B := Safe.reindex (LSub.appendRight _ _) hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B hSafe1
      refine ⟨C, Step.app2 hv1 hstepB, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have hv1' : LSub (locations v1) (dom B) := by
        intro x hx; exact hSafe.roots_covered x (List.mem_append.mpr (Or.inl hx))
      have hv1'' : LSub (locations v1) (dom C) := LSub.trans hv1' (Step.dom_mono hstepB)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hv1'' x h
      · exact hSafe'.roots_covered x h
  | @refV v n0 μ hv hfresh =>
      -- E-RefV：ここが Safe.lift との「向きの違い」が現れる箇所。
      -- 今度は A(=μ) 側の n0 ∉ dom μ が最初から与えられている（hfresh）。
      -- B 側の n0 ∉ dom B は、逆に dom_sub（dom B ⊆ dom A）の対偶で導く：
      -- もし n0 ∈ dom B なら dom_sub により n0 ∈ dom A となり hfresh と矛盾。
      intro B hSafe
      have hnB : n0 ∉ dom B := fun hmem => hfresh (hSafe.dom_sub n0 hmem)
      refine ⟨alloc B n0 v, Step.refV hv hnB, ?_, ?_, ?_, ?_, ?_⟩
      · intro l hl
        rw [mem_dom_alloc] at hl
        rcases hl with hl | hl
        · exact Nat.lt_succ_of_lt (hSafe.bounded l hl)
        · subst hl; exact Nat.lt_succ_self _
      · intro l hl
        rw [mem_dom_alloc] at hl ⊢
        rcases hl with hl | hl
        · exact Or.inl (hSafe.dom_sub l hl)
        · exact Or.inr hl
      · intro l hl
        simp only [locations, List.mem_singleton] at hl
        exact (mem_dom_alloc _ _ _ _).mpr (Or.inr hl)
      · intro l hl l' hl'
        rw [mem_dom_alloc] at hl
        rcases hl with hl | hl
        · have hlne : l ≠ n0 := fun he => hnB (he ▸ hl)
          have heq : locOf (alloc B n0 v) l = locOf B l := by
            unfold locOf; rw [lookup_alloc_other _ _ _ _ hlne]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.self_closed l hl l' hl'))
        · have heq : locOf (alloc B n0 v) l = locations v := by
            rw [hl]; unfold locOf; rw [lookup_alloc_same _ _ _ hnB]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.roots_covered l' hl'))
      · intro l hl
        rw [mem_dom_alloc] at hl
        rcases hl with hl | hl
        · have hlne : l ≠ n0 := fun he => hnB (he ▸ hl)
          rw [lookup_alloc_other _ _ _ _ hlne, hSafe.agree l hl, lookup_alloc_other _ _ _ _ hlne]
        · subst hl
          rw [lookup_alloc_same _ _ _ hnB, lookup_alloc_same _ _ _ hfresh]
  | @ref1 t0 t0' n n' μ μ' hsub ih =>
      intro B hSafe
      have hSafe0 : Safe t0 n μ B := hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B hSafe0
      exact ⟨C, Step.ref1 hstepB, hSafe'⟩
  | @derefLoc n μ l0 v0 hlk =>
      -- ここでも向きが逆：A(=μ) 側で l0 に v0 が入っている（hlk）ことが
      -- 最初から与えられ、B 側でも同じ v0 が入っていることを
      -- roots_covered（l0∈dom B）と agree（B と A の一致）から導く
      -- （Safe.lift の derefLoc ケースでは agree の向きが逆だった）
      intro B hSafe
      have hl0 : l0 ∈ dom B := hSafe.roots_covered l0 (by simp [locations])
      have hlkB : lookupOpt B l0 = some v0 := by rw [hSafe.agree l0 hl0, hlk]
      refine ⟨B, Step.derefLoc hlkB, hSafe.bounded, hSafe.dom_sub, ?_, hSafe.self_closed, hSafe.agree⟩
      have hlocOf : locOf B l0 = locations v0 := by unfold locOf; rw [hlkB]
      intro x hx
      apply hSafe.self_closed l0 hl0
      rw [hlocOf]; exact hx
  | @deref1 t0 t0' n n' μ μ' hsub ih =>
      intro B hSafe
      have hSafe0 : Safe t0 n μ B := hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B hSafe0
      exact ⟨C, Step.deref1 hstepB, hSafe'⟩
  | @assignLoc n0 μ l0 v0 hv0 hl0mem =>
      -- E-Assign（location版）：今度は A(=μ) 側の l0 ∈ dom μ が
      -- 与えられているが、実は B 側の l0 ∈ dom B は roots_covered
      -- （locations(assign(loc l0)v0) ⊆ dom B）だけから直接得られ、
      -- hl0mem（A 側の情報）はこの向きでは使う必要すらない
      intro B hSafe
      have hl0 : l0 ∈ dom B := hSafe.roots_covered l0 (by simp [locations])
      have hv0sub : LSub (locations v0) (dom B) := by
        intro x hx; exact hSafe.roots_covered x (by simp [locations]; exact Or.inr hx)
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
          rw [hlocOf] at hl'
          exact hv0sub l' hl'
        · have hlocOf : locOf (update B l0 v0) l = locOf B l := by
            unfold locOf; rw [lookup_update_other _ _ _ _ heq]
          rw [hlocOf] at hl'
          exact hSafe.self_closed l hl l' hl'
      · intro l hl
        rw [dom_update] at hl
        by_cases heq : l = l0
        · rw [heq, lookup_update_same _ _ _ hl0, lookup_update_same _ _ _ hl0mem]
        · rw [lookup_update_other _ _ _ _ heq, hSafe.agree l hl, lookup_update_other _ _ _ _ heq]
  | @assign1 t1 t1' t2 n n' μ μ' hsub ih =>
      intro B hSafe
      have hSafe1 : Safe t1 n μ B := Safe.reindex (LSub.appendLeft _ _) hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B hSafe1
      refine ⟨C, Step.assign1 hstepB, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have ht2 : LSub (locations t2) (dom B) := by
        intro x hx; exact hSafe.roots_covered x (List.mem_append.mpr (Or.inr hx))
      have ht2' : LSub (locations t2) (dom C) := LSub.trans ht2 (Step.dom_mono hstepB)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hSafe'.roots_covered x h
      · exact ht2' x h
  | @assign2 v1 t2 t2' n n' μ μ' hv1 hsub ih =>
      intro B hSafe
      have hSafe1 : Safe t2 n μ B := Safe.reindex (LSub.appendRight _ _) hSafe
      obtain ⟨C, hstepB, hSafe'⟩ := ih B hSafe1
      refine ⟨C, Step.assign2 hv1 hstepB, hSafe'.bounded, hSafe'.dom_sub, ?_, hSafe'.self_closed, hSafe'.agree⟩
      have hv1' : LSub (locations v1) (dom B) := by
        intro x hx; exact hSafe.roots_covered x (List.mem_append.mpr (Or.inl hx))
      have hv1'' : LSub (locations v1) (dom C) := LSub.trans hv1' (Step.dom_mono hstepB)
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hv1'' x h
      · exact hSafe'.roots_covered x h


/- ============================================================ -/
/-  The combined (ordinary ∪ garbage-collecting) evaluation       -/
/-  relation, and the correctness theorem itself                  -/
/-  「通常のステップ ∪ GCステップ」を合わせた評価関係と、             -/
/-  正しさの定理そのもの                                           -/
/- ============================================================ -/

/-- "`A` extends `B`": `A`'s domain contains `B`'s, and they agree on
    every location of `B`.  This is precisely the relationship between
    stores demanded by the printed solution's (5)-(a) and (5)-(b).

    「`A` は `B` を拡張する」：`A` の定義域は `B` の定義域を含み、
    `B` に含まれるすべての location で両者の値が一致する。
    これはまさに、模範解答の (5)-(a)／(5)-(b) が要求している
    ストア同士の関係そのもの。`Safe` から「GC が生きているかどうか」に
    関する条件（自己閉包・根の被覆・Bounded）を落としたもの、
    と考えるとよい。 -/
def Extends (A B : Store) : Prop :=
  LSub (dom B) (dom A) ∧ ∀ l, l ∈ dom B → lookupOpt B l = lookupOpt A l

-- 自分自身は自分自身を（自明に）拡張する
theorem Extends.refl (A : Store) : Extends A A := ⟨LSub.refl _, fun _ _ => rfl⟩

-- Safe の条件のうち (2)(5) だけを取り出せば Extends が得られる
theorem Safe.extends {t n A B} (h : Safe t n A B) : Extends A B := ⟨h.dom_sub, h.agree⟩

/-- `CombinedStep t n μ t' n' μ'` is one step of `→ ∪ →gc`: either an
    ordinary evaluation step, or an (E-GC) step (which leaves the term
    and the allocation counter unchanged, and only ever shrinks the
    store).

    `CombinedStep t n μ t' n' μ'` は「`→ ∪ →gc`」の1ステップ：
    通常の評価ステップか、あるいは (E-GC) ステップ
    （項と割り当てカウンタは変えず、ストアを縮めるだけ）のどちらか。 -/
def CombinedStep (t : Term) (n : Nat) (μ : Store) (t' : Term) (n' : Nat) (μ' : Store) : Prop :=
  Step t n μ t' n' μ' ∨ (t' = t ∧ n' = n ∧ GCStep t μ μ')

/-- Reflexive-transitive closure of `CombinedStep`, i.e. `→gc*` from the
    printed solution.

    `CombinedStep` の反射推移閉包、つまり模範解答でいう `→gc*`
    （通常のステップと (E-GC) ステップを好きな順序・好きな回数だけ
    組み合わせられる、という関係）。 -/
inductive CombinedStar : Term → Nat → Store → Term → Nat → Store → Prop where
  | refl {t n μ} : CombinedStar t n μ t n μ
  | tail {t n μ t' n' μ' t'' n'' μ''} :
      CombinedStar t n μ t' n' μ' → CombinedStep t' n' μ' t'' n'' μ'' →
      CombinedStar t n μ t'' n'' μ''

/-- Every ordinary evaluation is in particular a combined one (taking no
    (E-GC) steps at all).

    通常の評価は、特に「(E-GC) ステップを一切使わない」合成評価
    でもある——これが定理 (5)-(b) の証明で使う「自明な」埋め込み。 -/
theorem StepStar.toCombined {t n μ t' n' μ'} (h : StepStar t n μ t' n' μ') :
    CombinedStar t n μ t' n' μ' := by
  induction h with
  | refl => exact CombinedStar.refl
  | tail _ hstep ih => exact CombinedStar.tail ih (Or.inl hstep)

/-- The heart of the correctness theorem: a combined (`→ ∪ →gc`) run
    starting at a configuration `(t, n, μ)` that is `Safe` relative to
    some bigger store `A` can be *replayed*, step for step, as a purely
    ordinary run starting from `A`, landing in a configuration that is
    again `Safe`-related to the combined run's endpoint.  `Safe.lift`
    handles the ordinary-step case (replay on the bigger store) and
    `Safe.gc_absorb` handles the (E-GC) case (the bigger store doesn't
    need to move at all — garbage collection is invisible to it).

    正しさの定理の核心部分：ある構成 `(t, n, μ)` から始まる合成評価
    （`→ ∪ →gc` を何度も踏んだもの）が、より大きなストア `A` に対して
    `Safe` の関係にあるとき、その合成評価は `A` から出発する
    「純粋に通常のステップだけの実行」として、1ステップずつ
    「再生」できる。しかも再生後の構成同士も再び `Safe` の関係を保つ。

    `CombinedStar`（帰納的定義）自身の帰納法で証明する：
    ・`refl`（0ステップ）：A' := A、hSafe をそのまま返す
    ・`tail`（1ステップ追加）：帰納法の仮定 ih で「これまでの部分」を
      A 側で再生し、最後の1ステップを場合分けする：
        - 通常のステップだった場合：`Safe.lift` を使って、
          その1ステップも A 側で再生する
        - (E-GC) ステップだった場合：これは「小さい側（GCトラック）」
          だけの出来事なので、A 側は *何もステップを踏まなくてよい*
          ——ただ `Safe.gc_absorb` で Safe の関係を保つだけでよい
          （GCは大きい側からは見えない、ということ）。 -/
theorem CombinedStar.safe_lift {t n μ t' n' μ''} (h : CombinedStar t n μ t' n' μ'') :
    ∀ A, Safe t n A μ → ∃ A', StepStar t n A t' n' A' ∧ Safe t' n' A' μ'' := by
  induction h with
  | refl => intro A hSafe; exact ⟨A, StepStar.refl, hSafe⟩
  | tail _ hcs ih =>
      intro A hSafe
      obtain ⟨A1, hstar1, hSafe1⟩ := ih A hSafe
      cases hcs with
      | inl hstep =>
          -- 通常のステップ：Safe.lift で A 側にも同じステップを持ち上げる
          obtain ⟨A', hstepA, hSafe'⟩ := Safe.lift hstep A1 hSafe1
          exact ⟨A', StepStar.tail hstar1 hstepA, hSafe'⟩
      | inr hgc =>
          -- (E-GC) ステップ：A 側はそのまま、Safe.gc_absorb で関係を保つだけ
          obtain ⟨heqt, heqn, hgcstep⟩ := hgc
          subst heqt; subst heqn
          exact ⟨A1, hstar1, Safe.gc_absorb hSafe1 hgcstep⟩

/- ============================================================ -/
/-  Theorem 13.3.1(5), infinite-memory case                       -/
/-  定理 13.3.1(5)、無限メモリの場合                                -/
/- ============================================================ -/
/-
   Both directions are stated starting from a configuration `(t, μ)` at
   the very beginning of execution, with `μ` already well-formed in the
   trivial sense that it contains everything the *initial* term `t`
   names and that its own bindings are self-closed — for the standard
   case `μ = []` (no locations allocated yet) and `t` a *source* term
   (containing no bare `loc` literals, i.e. `locations t = []`), both
   hypotheses hold automatically.  `n = 0` is the natural starting
   allocation counter, but any bound on `μ` works.

   両方向とも、実行のごく最初の構成 `(t, μ)` から始まるとして述べる。
   `μ` はすでに「素朴な意味で整合的」——つまり *最初の* 項 `t` が
   名指ししているものをすべて含み、`μ` 自身の束縛も自己閉包している
   ——としている。標準的なケース（`μ = []`：まだ何も割り当てていない、
   `t` が生の `loc` リテラルを含まない「ソースプログラム」、すなわち
   `locations t = []`）では、これらの前提は自動的に満たされる。
   `n = 0` は自然な開始カウンタだが、`μ` に対する適切な上界であれば
   何でもよい。
-/

/-- **Theorem 13.3.1(5)-(a).**  If the garbage-collected run
    `(t, μ) →gc* (t', μ'')` is possible, then the plain (ordinary,
    uncollected) run `(t, μ) →* (t', μ')` is *also* possible, for some
    `μ'` whose domain contains `μ''`'s and which agrees with `μ''` on
    their common domain.

    **定理 13.3.1(5)-(a)。** GC付きの実行 `(t, μ) →gc* (t', μ'')` が
    可能ならば、通常の（GCなしの）実行 `(t, μ) →* (t', μ')` も *同様に*
    可能である。ここで `μ'` の定義域は `μ''` の定義域を含み、
    共通部分では値が一致する。

    証明は一行：初期状態が自分自身に対して自明に Safe である
    （`Safe.refl`）ことを示し、`CombinedStar.safe_lift`（上で示した
    「合成評価は通常評価として再生できる」補題）を適用し、最後に
    `Safe.extends` で `Safe` の関係から `Extends` の関係を取り出すだけ。 -/
theorem gc_correctness_5a {t : Term} {μ : Store} {n : Nat}
    (hbounded : Bounded n μ) (hroots : LSub (locations t) (dom μ))
    (hclosed : ∀ l, l ∈ dom μ → ∀ l', l' ∈ locOf μ l → l' ∈ dom μ)
    {t' : Term} {n' : Nat} {μ'' : Store}
    (h : CombinedStar t n μ t' n' μ'') :
    ∃ μ', StepStar t n μ t' n' μ' ∧ Extends μ' μ'' := by
  obtain ⟨μ', hstar, hSafe⟩ := h.safe_lift μ (Safe.refl hbounded hroots hclosed)
  exact ⟨μ', hstar, hSafe.extends⟩

/-- **Theorem 13.3.1(5)-(b), memory-safe (infinite-memory) case.**  If
    the plain run `(t, μ) →* (t', μ')` is possible, then there is *some*
    garbage-collected run `(t, μ) →gc* (t', μ'')` reaching the very same
    `t'`, with `μ'` extending `μ''`.  (Since memory is infinite here,
    clause (5)-(b)-ii of the printed solution — running out of memory —
    can never arise; per footnote †5 this refinement is optional, not
    required, for the theorem to hold.)  Taking `μ'' := μ'` itself (i.e.
    simply never invoking (E-GC)) already witnesses this, since every
    ordinary run is in particular a `→gc*` run.

    **定理 13.3.1(5)-(b)、メモリ安全（無限メモリ）の場合。**
    通常の実行 `(t, μ) →* (t', μ')` が可能ならば、*ある* GC付きの実行
    `(t, μ) →gc* (t', μ'')` が存在して、同じ `t'` に到達し、
    `μ'` がその `μ''` を拡張する。（メモリを無限にモデル化しているので、
    模範解答の (5)-(b)-(ii) 節——メモリ枯渇のケース——は決して起こらない。
    脚注†5のとおり、これは定理の成立に「必要な」精緻化ではなく
    「あってもよい」精緻化に過ぎない。）

    `μ'' := μ'` そのもの（すなわち (E-GC) を一度も呼ばない）を取れば、
    それだけでこの存在証明の証拠になる——通常の実行は、特に
    「`→gc*` の実行」でもあるので（`StepStar.toCombined`）。 -/
theorem gc_correctness_5b {t : Term} {n : Nat} {μ : Store}
    {t' : Term} {n' : Nat} {μ' : Store}
    (h : StepStar t n μ t' n' μ') :
    ∃ μ'', CombinedStar t n μ t' n' μ'' ∧ Extends μ' μ'' :=
  ⟨μ', h.toCombined, Extends.refl μ'⟩

end GC