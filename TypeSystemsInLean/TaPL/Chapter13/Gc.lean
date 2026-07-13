/-
  Exercise 13.3.1 (TAPL) — Modeling garbage collection.

  We formalize the fragment of "FullUntypedRef" relevant to Chapter 13
  (untyped call-by-value λ-calculus extended with mutable references),
  give it a small-step operational semantics threading an explicit store,
  add a garbage-collection step `→gc` exactly as described in the printed
  solution (13.3.1) using a semantic notion of *reachability*, and prove
  the correctness theorem that justifies the modification:

      (t, μ) →gc* (t', μ'')   implies   ∃ μ', (t, μ) →* (t', μ')
                                          and μ' ⊇ μ'' (domain-wise, agreeing
                                          on the common domain)                 [(5)-(a)]

      (t, μ) →*     (t', μ')  implies   ∃ μ'', (t, μ) →gc* (t', μ'')
                                          and μ' ⊇ μ'' (domain-wise, agreeing
                                          on the common domain)                 [(5)-(b), memory-safe case]

  Following the printed solution's own footnote (†5, from the errata),
  finiteness of the location set L is *not* required for this result; we
  therefore model the store's location set as all of `Nat`, i.e. memory is
  taken to be infinite.  This sidesteps clause (5)-(b)-ii (memory
  exhaustion), which the footnote explicitly says is an optional
  refinement, not a necessary one.  Everything below is proved with no
  `sorry`, using nothing beyond Lean 4's core library (no Mathlib).
-/

namespace GC

/- ============================================================ -/
/-  A little bit of list infrastructure (no Mathlib)             -/
/- ============================================================ -/

/-- "list inclusion" as a membership statement, spelled out so we don't
    need any library beyond `List.Mem`. -/
def LSub (l1 l2 : List Nat) : Prop := ∀ x, x ∈ l1 → x ∈ l2

theorem LSub.refl (l : List Nat) : LSub l l := fun _ h => h

theorem LSub.trans {l1 l2 l3 : List Nat} (h1 : LSub l1 l2) (h2 : LSub l2 l3) :
    LSub l1 l3 := fun x hx => h2 x (h1 x hx)

theorem LSub.appendLeft (l1 l2 : List Nat) : LSub l1 (l1 ++ l2) :=
  fun x hx => List.mem_append.mpr (Or.inl hx)

theorem LSub.appendRight (l1 l2 : List Nat) : LSub l2 (l1 ++ l2) :=
  fun x hx => List.mem_append.mpr (Or.inr hx)

theorem LSub.appendCongr {l1 l2 l1' l2' : List Nat}
    (h1 : LSub l1 l1') (h2 : LSub l2 l2') : LSub (l1 ++ l2) (l1' ++ l2') := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append.mpr (Or.inl (h1 x h))
  · exact List.mem_append.mpr (Or.inr (h2 x h))

/- ============================================================ -/
/-  Syntax (de Bruijn indices, as is standard for mechanization) -/
/- ============================================================ -/

/-- Terms of the untyped λ-calculus with `unit` and mutable references.
    `loc l` is a run-time store location; it never occurs in source
    programs, only in terms that arise during evaluation. -/
inductive Term where
  | var    : Nat → Term
  | abs    : Term → Term
  | app    : Term → Term → Term
  | unit   : Term
  | loc    : Nat → Term
  | ref    : Term → Term
  | deref  : Term → Term
  | assign : Term → Term → Term
  deriving DecidableEq, Repr

open Term

/-- Values. -/
inductive IsValue : Term → Prop where
  | vabs  : ∀ t, IsValue (abs t)
  | vunit : IsValue unit
  | vloc  : ∀ l, IsValue (loc l)

/- ---------------- shifting ---------------- -/

/-- Shift free variables (de Bruijn index ≥ `c`) up by `d`. -/
def shift (d : Nat) : Nat → Term → Term
  | c, var k      => if k ≥ c then var (k + d) else var k
  | c, abs t      => abs (shift d (c + 1) t)
  | c, app t1 t2  => app (shift d c t1) (shift d c t2)
  | _, unit       => unit
  | _, loc l      => loc l
  | c, ref t      => ref (shift d c t)
  | c, deref t    => deref (shift d c t)
  | c, assign t1 t2 => assign (shift d c t1) (shift d c t2)

/-- Shift free variables (index ≥ `c`) down by 1.  Used only in `substTop`,
    where it is applied to a term in which no free occurrence of index `c`
    remains (that occurrence having just been substituted away), so the
    shift is safe. -/
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

/-- `subst j s t` replaces free occurrences of variable `j` in `t` by `s`,
    adjusting indices as usual across binders. -/
def subst (j : Nat) (s : Term) : Term → Term
  | var k      => if k = j then s else var k
  | abs t      => abs (subst (j + 1) (shift 1 0 s) t)
  | app t1 t2  => app (subst j s t1) (subst j s t2)
  | unit       => unit
  | loc l      => loc l
  | ref t      => ref (subst j s t)
  | deref t    => deref (subst j s t)
  | assign t1 t2 => assign (subst j s t1) (subst j s t2)

/-- Beta-substitution at the top: `substTop s t` = `[0 ↦ s] t` used to
    implement `(λ.t) v --> substTop v t`. -/
def substTop (s t : Term) : Term := unshift 0 (subst 0 (shift 1 0 s) t)

/- ============================================================ -/
/-  Locations occurring (syntactically) in a term                -/
/- ============================================================ -/

/-- `locations t` is the (possibly-repeating) list of store locations that
    literally occur in `t`.  This is `locations(t)` from the printed
    solution. -/
def locations : Term → List Nat
  | var _        => []
  | abs t        => locations t
  | app t1 t2    => locations t1 ++ locations t2
  | unit         => []
  | loc l        => [l]
  | ref t        => locations t
  | deref t      => locations t
  | assign t1 t2 => locations t1 ++ locations t2

/-- `shift`/`unshift` only ever touch `var` nodes, so they leave the set of
    occurring locations completely unchanged. -/
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
    direction is exactly what is needed. -/
theorem locations_subst (j : Nat) (s t : Term) :
    LSub (locations (subst j s t)) (locations s ++ locations t) := by
  induction t generalizing j s with
  | var k =>
      simp only [subst]
      split
      · intro x hx
        exact List.mem_append.mpr (Or.inl hx)
      · intro x hx
        exact List.mem_append.mpr (Or.inr hx)
  | abs t ih =>
      simp only [subst, locations]
      intro x hx
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

/-- Corollary: `locations (substTop s t) ⊆ locations s ++ locations t`. -/
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
/- ============================================================ -/

/-- A store is a finite association list from locations to (value) terms,
    exactly as in TAPL: `µ ∈ Store ::= {x1 = h1, ..., xn = hn}`. -/
abbrev Store := List (Nat × Term)

/-- Domain of a store. -/
def dom (μ : Store) : List Nat := μ.map Prod.fst

/-- Look up a location; `none` if unbound.  Earlier bindings shadow later
    ones, matching the usual convention for association lists. -/
def lookupOpt (μ : Store) (l : Nat) : Option Term :=
  match μ with
  | [] => none
  | (l', v) :: μ => if l' = l then some v else lookupOpt μ l

theorem mem_dom_cons (l' : Nat) (v : Term) (μ : Store) (l : Nat) :
    l ∈ dom ((l', v) :: μ) ↔ l = l' ∨ l ∈ dom μ := by
  simp [dom]

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

/-- Update the value bound to an already-present location `l`. -/
def update (μ : Store) (l : Nat) (v : Term) : Store :=
  match μ with
  | [] => []
  | (l', v') :: μ => if l' = l then (l', v) :: μ else (l', v') :: update μ l v

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

theorem lookup_update_other (μ : Store) (l l' : Nat) (v : Term) (hne : l' ≠ l) :
    lookupOpt (update μ l v) l' = lookupOpt μ l' := by
  induction μ with
  | nil => rfl
  | cons p μ ih =>
      rcases p with ⟨k, w⟩
      by_cases hk : k = l
      · have hupd : update ((k, w) :: μ) l v = (k, v) :: μ := by
          unfold update; rw [if_pos hk]
        rw [hupd]
        have hkl' : ¬ k = l' := by rw [hk]; exact fun h => hne h.symm
        show (if k = l' then some v else lookupOpt μ l') = lookupOpt ((k, w) :: μ) l'
        rw [if_neg hkl']
        show lookupOpt μ l' = if k = l' then some w else lookupOpt μ l'
        rw [if_neg hkl']
      · have hupd : update ((k, w) :: μ) l v = (k, w) :: update μ l v := by
          show (if k = l then (k, v) :: μ else (k, w) :: update μ l v) = (k, w) :: update μ l v
          rw [if_neg hk]
        rw [hupd]
        show (if k = l' then some w else lookupOpt (update μ l v) l')
            = (if k = l' then some w else lookupOpt μ l')
        by_cases hk' : k = l'
        · rw [if_pos hk', if_pos hk']
        · rw [if_neg hk', if_neg hk']
          exact ih

/-- Allocating `l` (assumed fresh) with initial value `v`. -/
def alloc (μ : Store) (l : Nat) (v : Term) : Store := μ ++ [(l, v)]

theorem dom_alloc (μ : Store) (l : Nat) (v : Term) :
    dom (alloc μ l v) = dom μ ++ [l] := by
  simp [alloc, dom]

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

theorem mem_dom_alloc (μ : Store) (l l' : Nat) (v : Term) :
    l' ∈ dom (alloc μ l v) ↔ l' ∈ dom μ ∨ l' = l := by
  simp [alloc, dom]

theorem LSub_dom_alloc (μ : Store) (l : Nat) (v : Term) : LSub (dom μ) (dom (alloc μ l v)) :=
  fun x hx => (mem_dom_alloc μ l x v).mpr (Or.inl hx)

theorem mem_dom_update (μ : Store) (l l' : Nat) (v : Term) :
    l' ∈ dom (update μ l v) ↔ l' ∈ dom μ := by rw [dom_update]

/- ============================================================ -/
/-  Reachability                                                  -/
/- ============================================================ -/

/-- The locations occurring in the heap value bound to `l` (or `[]` if `l`
    is unbound). -/
def locOf (μ : Store) (l : Nat) : List Nat :=
  match lookupOpt μ l with
  | some v => locations v
  | none   => []

/-- `ReachableFrom roots μ l` says `l` is reachable, in the store `μ`, from
    the given set (list) of root locations — exactly the inductive closure
    described in the printed solution: `l'` is reachable if it is a root,
    or if it is one step reachable (`l' ∈ locations(µ(l))`) from some
    already-reachable `l`. -/
inductive ReachableFrom (roots : List Nat) (μ : Store) : Nat → Prop where
  | base {l}  : l ∈ roots → ReachableFrom roots μ l
  | step {l l'} : ReachableFrom roots μ l → l' ∈ locOf μ l → ReachableFrom roots μ l'

/-- Reachability from a term `t` in a store `µ`: `reachable(t, µ)` from the
    printed solution. -/
def Reachable (t : Term) (μ : Store) (l : Nat) : Prop := ReachableFrom (locations t) μ l

/-- Reachability is monotone in the root set. -/
theorem ReachableFrom.mono {roots1 roots2 : List Nat} (h : LSub roots1 roots2)
    {μ : Store} {l : Nat} (hr : ReachableFrom roots1 μ l) : ReachableFrom roots2 μ l := by
  induction hr with
  | base hl => exact .base (h _ hl)
  | step _ hl' ih => exact .step ih hl'

theorem Reachable.mono {t1 t2 : Term} (h : LSub (locations t1) (locations t2))
    {μ : Store} {l : Nat} (hr : Reachable t1 μ l) : Reachable t2 μ l :=
  ReachableFrom.mono h hr

/-- Reachability only ever depends on `µ` through the bindings at
    reachable locations: if two stores agree on all locations reachable
    from a common root set, the *same* locations are reachable from those
    roots in both stores.  This is the basic "locality" fact underlying
    the whole development. -/
theorem ReachableFrom.agree {roots : List Nat} {μ1 μ2 : Store}
    (hagree : ∀ l, ReachableFrom roots μ1 l → lookupOpt μ1 l = lookupOpt μ2 l)
    {l : Nat} (hr : ReachableFrom roots μ1 l) : ReachableFrom roots μ2 l := by
  induction hr with
  | base hl => exact .base hl
  | @step l l' hprev hl' ih =>
      have heq : lookupOpt μ1 l = lookupOpt μ2 l := hagree l hprev
      apply ReachableFrom.step ih
      unfold locOf at hl' ⊢
      rw [← heq]
      exact hl'

/- ============================================================ -/
/-  The garbage-collection step                                   -/
/- ============================================================ -/

/-- `GCStep t μ μ'` says `μ'` is exactly `µ` restricted to
    `reachable(t, µ)`, i.e. this is precisely rule (E-GC) from the printed
    solution: "µ′ is the restriction of µ to reachable(t, µ)". -/
def GCStep (t : Term) (μ μ' : Store) : Prop :=
  (∀ l, l ∈ dom μ' ↔ (l ∈ dom μ ∧ Reachable t μ l)) ∧
  (∀ l, l ∈ dom μ' → lookupOpt μ' l = lookupOpt μ l)

/- ============================================================ -/
/-  Ordinary (non-GC) evaluation                                  -/
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
    non-issue.) -/
inductive Step : Term → Nat → Store → Term → Nat → Store → Prop where
  | appAbs {t v n μ} : IsValue v → Step (app (abs t) v) n μ (substTop v t) n μ
  | app1 {t1 t1' t2 n n' μ μ'} :
      Step t1 n μ t1' n' μ' → Step (app t1 t2) n μ (app t1' t2) n' μ'
  | app2 {v1 t2 t2' n n' μ μ'} :
      IsValue v1 → Step t2 n μ t2' n' μ' → Step (app v1 t2) n μ (app v1 t2') n' μ'
  | refV {v n μ} : IsValue v → n ∉ dom μ →
      Step (ref v) n μ (loc n) (n + 1) (alloc μ n v)
  | ref1 {t t' n n' μ μ'} : Step t n μ t' n' μ' → Step (ref t) n μ (ref t') n' μ'
  | derefLoc {n μ l v} : lookupOpt μ l = some v → Step (deref (loc l)) n μ v n μ
  | deref1 {t t' n n' μ μ'} : Step t n μ t' n' μ' → Step (deref t) n μ (deref t') n' μ'
  | assignLoc {n μ l v} : IsValue v → l ∈ dom μ →
      Step (assign (loc l) v) n μ unit n (update μ l v)
  | assign1 {t1 t1' t2 n n' μ μ'} :
      Step t1 n μ t1' n' μ' → Step (assign t1 t2) n μ (assign t1' t2) n' μ'
  | assign2 {v1 t2 t2' n n' μ μ'} : IsValue v1 → Step t2 n μ t2' n' μ' →
      Step (assign v1 t2) n μ (assign v1 t2') n' μ'

/-- Reflexive-transitive closure of `Step`, i.e. `→*`. -/
inductive StepStar : Term → Nat → Store → Term → Nat → Store → Prop where
  | refl {t n μ} : StepStar t n μ t n μ
  | tail {t n μ t' n' μ' t'' n'' μ''} :
      StepStar t n μ t' n' μ' → Step t' n' μ' t'' n'' μ'' → StepStar t n μ t'' n'' μ''

theorem StepStar.single {t n μ t' n' μ'} (h : Step t n μ t' n' μ') :
    StepStar t n μ t' n' μ' := StepStar.tail StepStar.refl h

theorem StepStar.trans {t1 n1 μ1 t2 n2 μ2 t3 n3 μ3}
    (h1 : StepStar t1 n1 μ1 t2 n2 μ2) (h2 : StepStar t2 n2 μ2 t3 n3 μ3) :
    StepStar t1 n1 μ1 t3 n3 μ3 := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact StepStar.tail ih hstep

/- ============================================================ -/
/-  Structural ("locality") lemmas about `Step`                   -/
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
-/

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
  | assignLoc _ _ => rw [dom_update]; exact LSub.refl _
  | assign1 _ ih => exact ih
  | assign2 _ _ ih => exact ih

theorem Step.new_loc_in_result {t n μ t' n' μ'} (h : Step t n μ t' n' μ') :
    ∀ l, l ∈ dom μ' → l ∉ dom μ → l ∈ locations t' := by
  induction h with
  | appAbs _ => intro l hl' hl; exact absurd hl' hl
  | app1 _ ih =>
      intro l hl' hl
      exact List.mem_append.mpr (Or.inl (ih l hl' hl))
  | app2 _ _ ih =>
      intro l hl' hl
      exact List.mem_append.mpr (Or.inr (ih l hl' hl))
  | @refV v n0 μ0 _ hfresh =>
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
      intro l hl' hl
      rw [mem_dom_update] at hl'
      exact absurd hl' hl
  | assign1 _ ih =>
      intro l hl' hl
      exact List.mem_append.mpr (Or.inl (ih l hl' hl))
  | assign2 _ _ ih =>
      intro l hl' hl
      exact List.mem_append.mpr (Or.inr (ih l hl' hl))

theorem Step.changed_loc_in_source {t n μ t' n' μ'} (h : Step t n μ t' n' μ') :
    ∀ l, l ∈ dom μ → lookupOpt μ l ≠ lookupOpt μ' l → l ∈ locations t := by
  induction h with
  | appAbs _ => intro l _ hne; exact absurd rfl hne
  | app1 _ ih =>
      intro l hl hne
      exact List.mem_append.mpr (Or.inl (ih l hl hne))
  | app2 _ _ ih =>
      intro l hl hne
      exact List.mem_append.mpr (Or.inr (ih l hl hne))
  | @refV v n0 μ0 _ hfresh =>
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
/- ============================================================ -/

/-- `Bounded n μ` says every location currently in the store is `< n`:
    i.e. `n` (and everything above it) is available for fresh
    allocation.  `Step` maintains this invariant, and — crucially — the
    counter `n` only ever increases, so a location once used is *never*
    reused, even if garbage collection later frees it. -/
def Bounded (n : Nat) (μ : Store) : Prop := ∀ l, l ∈ dom μ → l < n

theorem Bounded.mono {n μ} (h : Bounded n μ) : n ∉ dom μ := fun hmem => Nat.lt_irrefl n (h n hmem)

theorem Bounded.weaken {n n' μ} (h : Bounded n μ) (hle : n ≤ n') : Bounded n' μ :=
  fun l hl => Nat.lt_of_lt_of_le (h l hl) hle

theorem Bounded.subset {n μ μ'} (h : Bounded n μ) (hsub : LSub (dom μ') (dom μ)) :
    Bounded n μ' := fun l hl => h l (hsub l hl)

theorem Step.preserves_bounded {t n μ t' n' μ'} (h : Step t n μ t' n' μ')
    (hb : Bounded n μ) : n ≤ n' ∧ Bounded n' μ' := by
  induction h with
  | appAbs _ => exact ⟨Nat.le_refl _, hb⟩
  | @app1 t1 t1' t2 n n' μ μ' _ ih => exact ih hb
  | @app2 v1 t2 t2' n n' μ μ' _ _ ih => exact ih hb
  | @refV v n0 μ0 _ hfresh =>
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
      refine ⟨Nat.le_refl _, ?_⟩
      intro l hl
      rw [mem_dom_update] at hl
      exact hb l hl
  | @assign1 t1 t1' t2 n n' μ μ' _ ih => exact ih hb
  | @assign2 v1 t2 t2' n n' μ μ' _ _ ih => exact ih hb

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
/- ============================================================ -/

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
    the crux of the whole argument. -/
def Safe (t : Term) (n : Nat) (A B : Store) : Prop :=
  Bounded n A ∧
  LSub (dom B) (dom A) ∧
  LSub (locations t) (dom B) ∧
  (∀ l, l ∈ dom B → ∀ l', l' ∈ locOf B l → l' ∈ dom B) ∧
  (∀ l, l ∈ dom B → lookupOpt B l = lookupOpt A l)

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
    `self_closed`. -/
theorem Safe.reachable_in_dom {t n A B} (h : Safe t n A B) :
    ∀ l, Reachable t B l → l ∈ dom B := by
  intro l hr
  induction hr with
  | base hl => exact h.roots_covered _ hl
  | step hprev hl' ih => exact h.self_closed _ ih _ hl'

/-- Shrinking the term (i.e. only asking `Safe` to cover a *sub*set of
    the original term's locations) is always harmless: everything else
    about `Safe` is entirely term-independent. -/
theorem Safe.reindex {t1 t2 n A B} (hsub : LSub (locations t2) (locations t1))
    (h : Safe t1 n A B) : Safe t2 n A B :=
  ⟨h.bounded, h.dom_sub, fun l hl => h.roots_covered _ (hsub l hl), h.self_closed, h.agree⟩

theorem Safe.refl {t n A} (hb : Bounded n A) (hroots : LSub (locations t) (dom A))
    (hclosed : ∀ l, l ∈ dom A → ∀ l', l' ∈ locOf A l → l' ∈ dom A) : Safe t n A A :=
  ⟨hb, LSub.refl _, hroots, hclosed, fun _ _ => rfl⟩

/-- Absorbing an (E-GC) step on the safe side: collecting further never
    breaks `Safe`. -/
theorem Safe.gc_absorb {t n A B C} (h : Safe t n A B) (hgc : GCStep t B C) :
    Safe t n A C := by
  have hreachB : ∀ l, Reachable t B l → l ∈ dom B := h.reachable_in_dom
  refine ⟨h.bounded, ?_, ?_, ?_, ?_⟩
  · -- dom C ⊆ dom A
    intro l hl
    have := (hgc.1 l).mp hl
    exact h.dom_sub _ this.1
  · -- locations t ⊆ dom C
    intro l hl
    have h1 : l ∈ dom B := h.roots_covered _ hl
    have h2 : Reachable t B l := ReachableFrom.base hl
    exact (hgc.1 l).mpr ⟨h1, h2⟩
  · -- C self-closed
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
  · -- C agrees with A
    intro l hl
    have hlB : l ∈ dom B := ((hgc.1 l).mp hl).1
    rw [hgc.2 l hl, h.agree l hlB]


/- ============================================================ -/
/-  The two commutation ("Up"/"Down") lemmas                      -/
/- ============================================================ -/

/-- **"Up" / lifting lemma.**  If the *safe* (already partly
    garbage-collected) store `B` can take an ordinary step, then the
    *big* store `A` (of which `B` is a safe sub-store) can take the
    *identical* step (same term, same allocation counter), landing in a
    configuration that is again related by `Safe`.  This is what lets us
    replay a garbage-collected run as an ordinary (uncollected) run: see
    the header comment for why the shared allocation counter is what
    makes "the identical step" meaningful. -/
theorem Safe.lift {t n B t' n' C} (hstep : Step t n B t' n' C) :
    ∀ A, Safe t n A B → ∃ A', Step t n A t' n' A' ∧ Safe t' n' A' C := by
  induction hstep with
  | @appAbs t0 v n μ hv =>
      intro A hSafe
      refine ⟨A, Step.appAbs hv, ?_⟩
      apply Safe.reindex (t1 := app (abs t0) v) ?_ hSafe
      intro x hx
      have h1 := locations_substTop v t0 x hx
      exact LSub_append_comm _ _ x h1
  | @app1 t1 t1' t2 n n' μ μ' hsub ih =>
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
      intro A hSafe
      have hnA : n0 ∉ dom A := hSafe.bounded.mono
      refine ⟨alloc A n0 v, Step.refV hv hnA, ?_, ?_, ?_, ?_, ?_⟩
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
        · have hlne : l ≠ n0 := fun he => hfresh (he ▸ hl)
          have heq : locOf (alloc μ n0 v) l = locOf μ l := by
            unfold locOf; rw [lookup_alloc_other _ _ _ _ hlne]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.self_closed l hl l' hl'))
        · have heq : locOf (alloc μ n0 v) l = locations v := by
            rw [hl]; unfold locOf; rw [lookup_alloc_same _ _ _ hfresh]
          rw [heq] at hl'
          exact (mem_dom_alloc _ _ _ _).mpr (Or.inl (hSafe.roots_covered l' hl'))
      · intro l hl
        rw [mem_dom_alloc] at hl
        rcases hl with hl | hl
        · have hlne : l ≠ n0 := fun he => hfresh (he ▸ hl)
          rw [lookup_alloc_other _ _ _ _ hlne, hSafe.agree l hl, lookup_alloc_other _ _ _ _ hlne]
        · subst hl
          rw [lookup_alloc_same _ _ _ hfresh, lookup_alloc_same _ _ _ hnA]
  | @ref1 t0 t0' n n' μ μ' hsub ih =>
      intro A hSafe
      have hSafe0 : Safe t0 n A μ := hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe0
      exact ⟨A', Step.ref1 hstepA, hSafe'⟩
  | @derefLoc n μ l0 v0 hlk =>
      intro A hSafe
      have hl0 : l0 ∈ dom μ := hSafe.roots_covered l0 (by simp [locations])
      have hlkA : lookupOpt A l0 = some v0 := by rw [← hSafe.agree l0 hl0, hlk]
      refine ⟨A, Step.derefLoc hlkA, hSafe.bounded, hSafe.dom_sub, ?_, hSafe.self_closed, hSafe.agree⟩
      have hlocOf : locOf μ l0 = locations v0 := by unfold locOf; rw [hlk]
      intro x hx
      apply hSafe.self_closed l0 hl0
      rw [hlocOf]; exact hx
  | @deref1 t0 t0' n n' μ μ' hsub ih =>
      intro A hSafe
      have hSafe0 : Safe t0 n A μ := hSafe
      obtain ⟨A', hstepA, hSafe'⟩ := ih A hSafe0
      exact ⟨A', Step.deref1 hstepA, hSafe'⟩
  | @assignLoc n0 μ l0 v0 hv0 hl0mem =>
      intro A hSafe
      have hl0 : l0 ∈ dom μ := hSafe.roots_covered l0
        (by simp [locations])
      have hl0A : l0 ∈ dom A := hSafe.dom_sub l0 hl0
      have hv0sub : LSub (locations v0) (dom μ) := by
        intro x hx; exact hSafe.roots_covered x (by simp [locations]; exact Or.inr hx)
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
          rw [hlocOf] at hl'
          exact hv0sub l' hl'
        · have hlocOf : locOf (update μ l0 v0) l = locOf μ l := by
            unfold locOf; rw [lookup_update_other _ _ _ _ heq]
          rw [hlocOf] at hl'
          exact hSafe.self_closed l hl l' hl'
      · intro l hl
        rw [dom_update] at hl
        by_cases heq : l = l0
        · rw [heq, lookup_update_same _ _ _ hl0, lookup_update_same _ _ _ hl0A]
        · rw [lookup_update_other _ _ _ _ heq, hSafe.agree l hl, lookup_update_other _ _ _ _ heq]
  | @assign1 t1 t1' t2 n n' μ μ' hsub ih =>
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
    garbage-collected one. -/
theorem Safe.down {t n A t' n' A'} (hstep : Step t n A t' n' A') :
    ∀ B, Safe t n A B → ∃ C, Step t n B t' n' C ∧ Safe t' n' A' C := by
  induction hstep with
  | @appAbs t0 v n μ hv =>
      intro B hSafe
      refine ⟨B, Step.appAbs hv, ?_⟩
      apply Safe.reindex (t1 := app (abs t0) v) ?_ hSafe
      intro x hx
      have h1 := locations_substTop v t0 x hx
      exact LSub_append_comm _ _ x h1
  | @app1 t1 t1' t2 n n' μ μ' hsub ih =>
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
/- ============================================================ -/

/-- "`A` extends `B`": `A`'s domain contains `B`'s, and they agree on
    every location of `B`.  This is precisely the relationship between
    stores demanded by the printed solution's (5)-(a) and (5)-(b). -/
def Extends (A B : Store) : Prop :=
  LSub (dom B) (dom A) ∧ ∀ l, l ∈ dom B → lookupOpt B l = lookupOpt A l

theorem Extends.refl (A : Store) : Extends A A := ⟨LSub.refl _, fun _ _ => rfl⟩

theorem Safe.extends {t n A B} (h : Safe t n A B) : Extends A B := ⟨h.dom_sub, h.agree⟩

/-- `CombinedStep t n μ t' n' μ'` is one step of `→ ∪ →gc`: either an
    ordinary evaluation step, or an (E-GC) step (which leaves the term
    and the allocation counter unchanged, and only ever shrinks the
    store). -/
def CombinedStep (t : Term) (n : Nat) (μ : Store) (t' : Term) (n' : Nat) (μ' : Store) : Prop :=
  Step t n μ t' n' μ' ∨ (t' = t ∧ n' = n ∧ GCStep t μ μ')

/-- Reflexive-transitive closure of `CombinedStep`, i.e. `→gc*` from the
    printed solution. -/
inductive CombinedStar : Term → Nat → Store → Term → Nat → Store → Prop where
  | refl {t n μ} : CombinedStar t n μ t n μ
  | tail {t n μ t' n' μ' t'' n'' μ''} :
      CombinedStar t n μ t' n' μ' → CombinedStep t' n' μ' t'' n'' μ'' →
      CombinedStar t n μ t'' n'' μ''

/-- Every ordinary evaluation is in particular a combined one (taking no
    (E-GC) steps at all). -/
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
    need to move at all — garbage collection is invisible to it). -/
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

/- ============================================================ -/
/-  Theorem 13.3.1(5), infinite-memory case                       -/
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
-/

/-- **Theorem 13.3.1(5)-(a).**  If the garbage-collected run
    `(t, μ) →gc* (t', μ'')` is possible, then the plain (ordinary,
    uncollected) run `(t, μ) →* (t', μ')` is *also* possible, for some
    `μ'` whose domain contains `μ''`'s and which agrees with `μ''` on
    their common domain. -/
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
    ordinary run is in particular a `→gc*` run. -/
theorem gc_correctness_5b {t : Term} {n : Nat} {μ : Store}
    {t' : Term} {n' : Nat} {μ' : Store}
    (h : StepStar t n μ t' n' μ') :
    ∃ μ'', CombinedStar t n μ t' n' μ'' ∧ Extends μ' μ'' :=
  ⟨μ', h.toCombined, Extends.refl μ'⟩

end GC