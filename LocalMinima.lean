/-!
# Deterministic lemmas about strict local minima on the line (Task 1)

Priorities are an arbitrary function `U : Int → Int` (only strict comparisons matter, so
this covers real priorities through their ranks on any finite window).
A root is a strict local minimum; `gapAt U g j` says that `j` and `j+g` are roots and no
site strictly between them is a root, i.e. the indicator `Y_j^{(g)}` equals one.

Formalised facts used in the proof of Task 1:
* `not_isMin_succ`: two adjacent sites are never both roots;
* `gap_overlap_small`, `gap_overlap_succ`: `Y_j Y_{j+h} = 0` for `1 ≤ h ≤ g-1` and `h = g+1`
  (so only the lags `h = g` and `h = g+2` contribute to the covariance sum);
* `gap_locality`: `Y_j` depends only on `U (j-1), …, U (j+g+1)` (finite dependence);
* `gap_inside_anchors`: fixed roots (anchors) at `A` and `A+2g` separate gaps;
* `good_block_*`: the anchor/guard structure of a good block and the two interior
  patterns with `H = 0` and `H = 2`.
-/

namespace LM

variable (U : Int → Int)

def isMin (j : Int) : Prop := U j < U (j - 1) ∧ U j < U (j + 1)

def gapAt (g : Nat) (j : Int) : Prop :=
  isMin U j ∧ isMin U (j + g) ∧ ∀ t : Int, 0 < t → t < g → ¬ isMin U (j + t)

theorem not_isMin_succ (j : Int) (h : isMin U j) : ¬ isMin U (j + 1) := by
  intro h'
  have e : U (j + 1 - 1) = U j := congrArg U (by omega)
  have := h.2; have := h'.1; omega

/-- `Y_j Y_{j+h} = 0` for `0 < h < g`. -/
theorem gap_overlap_small (g : Nat) (j h : Int) (h0 : 0 < h) (hg : h < g)
    (h1 : gapAt U g j) (h2 : gapAt U g (j + h)) : False :=
  h1.2.2 h h0 hg h2.1

/-- `Y_j Y_{j+g+1} = 0`. -/
theorem gap_overlap_succ (g : Nat) (j : Int)
    (h1 : gapAt U g j) (h2 : gapAt U g (j + (g + 1))) : False := by
  have e : j + ((g : Int) + 1) = (j + g) + 1 := by omega
  rw [e] at h2
  exact not_isMin_succ U _ h1.2.1 h2.1

/-- Locality: `gapAt U g j` only depends on the priorities in `[j-1, j+g+1]`. -/
theorem gap_locality (g : Nat) (j : Int) (V : Int → Int)
    (hUV : ∀ k, j - 1 ≤ k → k ≤ j + g + 1 → U k = V k) :
    gapAt U g j ↔ gapAt V g j := by
  have hmin : ∀ k, j ≤ k → k ≤ j + g → (isMin U k ↔ isMin V k) := by
    intro k hk1 hk2
    unfold isMin
    rw [hUV k (by omega) (by omega), hUV (k - 1) (by omega) (by omega),
      hUV (k + 1) (by omega) (by omega)]
  unfold gapAt
  rw [hmin j (by omega) (by omega), hmin (j + g) (by omega) (by omega)]
  constructor
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, fun t t0 tg ht => c t t0 tg ?_⟩
    exact (hmin (j + t) (by omega) (by omega)).2 ht
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, fun t t0 tg ht => c t t0 tg ?_⟩
    exact (hmin (j + t) (by omega) (by omega)).1 ht

/-- A root strictly inside a gap is impossible. -/
theorem no_root_inside_gap (g : Nat) (j A : Int) (hA : isMin U A)
    (hgap : gapAt U g j) (h1 : j < A) (h2 : A < j + g) : False := by
  have e : j + (A - j) = A := by omega
  have := hgap.2.2 (A - j) (by omega) (by omega)
  rw [e] at this
  exact this hA

/-- Anchors separate gaps: a gap meeting the open segment `(A, A+2g)` lies inside `[A, A+2g]`. -/
theorem gap_inside_anchors (g : Nat) (A j : Int) (hA : isMin U A) (hB : isMin U (A + 2 * g))
    (hgap : gapAt U g j) (h1 : j < A + 2 * g) (h2 : A < j + g) :
    A ≤ j ∧ j + g ≤ A + 2 * g := by
  constructor
  · by_cases hj : A ≤ j
    · exact hj
    · exact (no_root_inside_gap U g j A hA hgap (by omega) h2).elim
  · by_cases hj : j + g ≤ A + 2 * g
    · exact hj
    · exact (no_root_inside_gap U g j (A + 2 * g) hB hgap h1 (by omega)).elim

/-! ### Good blocks
A block is `A-1, A, A+1, …, A+2g-1, A+2g, A+2g+1` (guard, anchor, interior, anchor, guard).
It is *good* (threshold `c`) when both anchors are `< c` and all interior and guard
priorities are `> c` (in the paper: anchors `< 1/4`, interior `> 1/4`, guards `> 3/4`). -/

structure Good (g : Nat) (A c : Int) : Prop where
  g2 : 2 ≤ g
  anchorL : U A < c
  anchorR : U (A + 2 * g) < c
  guardL : c < U (A - 1)
  guardR : c < U (A + 2 * g + 1)
  interior : ∀ k, A < k → k < A + 2 * g → c < U k

variable {U}

theorem Good.isMin_left {g : Nat} {A c : Int} (hb : Good U g A c) : isMin U A :=
  ⟨by have := hb.guardL; have := hb.anchorL; omega,
   by have := hb.interior (A + 1) (by omega) (by have := hb.g2; omega)
      have := hb.anchorL; omega⟩

theorem Good.isMin_right {g : Nat} {A c : Int} (hb : Good U g A c) : isMin U (A + 2 * g) :=
  ⟨by have := hb.interior (A + 2 * g - 1) (by have := hb.g2; omega) (by omega)
      have := hb.anchorR; omega,
   by have := hb.guardR; have := hb.anchorR; omega⟩

theorem Good.guard_left_not_min {g : Nat} {A c : Int} (hb : Good U g A c) : ¬ isMin U (A - 1) := by
  intro h
  have e : U (A - 1 + 1) = U A := congrArg U (by omega)
  have := h.2; have := hb.anchorL; have := hb.guardL; omega

theorem Good.guard_right_not_min {g : Nat} {A c : Int} (hb : Good U g A c) :
    ¬ isMin U (A + 2 * g + 1) := by
  intro h
  have e : U (A + 2 * g + 1 - 1) = U (A + 2 * g) := congrArg U (by omega)
  have := h.1; have := hb.anchorR; have := hb.guardR; omega

/-- Interior sites next to the anchors are never roots. -/
theorem Good.first_interior_not_min {g : Nat} {A c : Int} (hb : Good U g A c) :
    ¬ isMin U (A + 1) := by
  intro h
  have e : U (A + 1 - 1) = U A := congrArg U (by omega)
  have := h.1; have := hb.anchorL
  have := hb.interior (A + 1) (by omega) (by have := hb.g2; omega); omega

theorem Good.last_interior_not_min {g : Nat} {A c : Int} (hb : Good U g A c) :
    ¬ isMin U (A + 2 * g - 1) := by
  intro h
  have e : U (A + 2 * g - 1 + 1) = U (A + 2 * g) := congrArg U (by omega)
  have := h.2; have := hb.anchorR
  have := hb.interior (A + 2 * g - 1) (by have := hb.g2; omega) (by omega); omega

/-- Pattern (a): increasing interior ⇒ no interior root. -/
theorem Good.increasing_no_interior_min {g : Nat} {A c : Int} (hb : Good U g A c)
    (hinc : ∀ k, A < k → k + 1 < A + 2 * g → U k < U (k + 1)) :
    ∀ k, A < k → k < A + 2 * g → ¬ isMin U k := by
  intro k hk1 hk2 h
  by_cases hk : k = A + 1
  · subst hk; exact hb.first_interior_not_min h
  · have := hinc (k - 1) (by omega) (by omega)
    have e : U (k - 1 + 1) = U k := congrArg U (by omega)
    have := h.1; omega

/-- In pattern (a), `H = 0`: no gap of length `g` inside `[A, A+2g]`. -/
theorem Good.increasing_H_zero {g : Nat} {A c : Int} (hb : Good U g A c)
    (hinc : ∀ k, A < k → k + 1 < A + 2 * g → U k < U (k + 1)) :
    ∀ j, A ≤ j → j + g ≤ A + 2 * g → ¬ gapAt U g j := by
  intro j hj1 hj2 hgap
  have g2 := hb.g2
  have hno := hb.increasing_no_interior_min hinc
  -- j is a root in [A, A+g], hence j = A; then j+g = A+g is an interior root
  by_cases hjA : j = A
  · subst hjA
    exact hno (j + g) (by omega) (by omega) hgap.2.1
  · exact hno j (by omega) (by omega) hgap.1

/-- Pattern (b): `U (A+g)` is the least interior value, the interior increases on
`A+1..A+g-1` and decreases on `A+g+1..A+2g-1`.  Then the interior roots are exactly `{A+g}`. -/
theorem Good.pattern_b_roots {g : Nat} {A c : Int} (hb : Good U g A c)
    (hleast : ∀ k, A < k → k < A + 2 * g → k ≠ A + g → U (A + g) < U k)
    (hinc : ∀ k, A < k → k + 1 < A + g → U k < U (k + 1))
    (hdec : ∀ k, A + g < k → k + 1 < A + 2 * g → U (k + 1) < U k) :
    ∀ k, A < k → k < A + 2 * g → (isMin U k ↔ k = A + g) := by
  have g2 := hb.g2
  intro k hk1 hk2
  constructor
  · intro h
    by_cases hk : k = A + g
    · exact hk
    · exfalso
      by_cases hlt : k < A + g
      · by_cases hk1' : k = A + 1
        · subst hk1'; exact hb.first_interior_not_min h
        · have := hinc (k - 1) (by omega) (by omega)
          have e : U (k - 1 + 1) = U k := congrArg U (by omega)
          have := h.1; omega
      · by_cases hkl : k = A + 2 * g - 1
        · subst hkl; exact hb.last_interior_not_min h
        · have := hdec k (by omega) (by omega)
          have := h.2; omega
  · intro hk
    subst hk
    exact ⟨hleast (A + g - 1) (by omega) (by omega) (by omega),
           hleast (A + g + 1) (by omega) (by omega) (by omega)⟩

/-- In pattern (b), `H = 2`: the gaps of length `g` inside `[A, A+2g]` are exactly those
starting at `A` and at `A+g`. -/
theorem Good.pattern_b_H_two {g : Nat} {A c : Int} (hb : Good U g A c)
    (hleast : ∀ k, A < k → k < A + 2 * g → k ≠ A + g → U (A + g) < U k)
    (hinc : ∀ k, A < k → k + 1 < A + g → U k < U (k + 1))
    (hdec : ∀ k, A + g < k → k + 1 < A + 2 * g → U (k + 1) < U k) :
    ∀ j, A ≤ j → j + g ≤ A + 2 * g → (gapAt U g j ↔ (j = A ∨ j = A + g)) := by
  have g2 := hb.g2
  have hr := hb.pattern_b_roots hleast hinc hdec
  have hmidMin : isMin U (A + g) := (hr (A + g) (by omega) (by omega)).2 rfl
  intro j hj1 hj2
  constructor
  · intro hgap
    by_cases hjA : j = A
    · exact Or.inl hjA
    · by_cases hjg : j = A + g
      · exact Or.inr hjg
      · exfalso
        exact hjg ((hr j (by omega) (by omega)).1 hgap.1)
  · intro hj
    cases hj with
    | inl hjA =>
      subst hjA
      refine ⟨hb.isMin_left, hmidMin, ?_⟩
      intro t t0 tg ht
      have := (hr (j + t) (by omega) (by omega)).1 ht; omega
    | inr hjg =>
      subst hjg
      have e : A + (g : Int) + g = A + 2 * g := by omega
      refine ⟨hmidMin, e ▸ hb.isMin_right, ?_⟩
      intro t t0 tg ht
      have := (hr (A + g + t) (by omega) (by omega)).1 ht; omega

/-! ### Blocks of general span (used for the local CLT in Task 3)
Anchors at `A` and `A+S`; with `S = 2g+1` the single-interior-root pattern has `H = 1`,
while the increasing pattern has `H = 0`, giving a lattice-span-one "Bernoulli part". -/

structure GoodS (U : Int → Int) (g S : Nat) (A c : Int) : Prop where
  g2 : 2 ≤ g
  span : g + 2 ≤ S
  anchorL : U A < c
  anchorR : U (A + S) < c
  interior : ∀ k, A < k → k < A + S → c < U k

theorem GoodS.first_not_min {g S : Nat} {A c : Int} (hb : GoodS U g S A c) :
    ¬ isMin U (A + 1) := by
  intro h
  have e : U (A + 1 - 1) = U A := congrArg U (by omega)
  have := h.1; have := hb.anchorL
  have := hb.interior (A + 1) (by omega) (by have := hb.span; omega); omega

theorem GoodS.last_not_min {g S : Nat} {A c : Int} (hb : GoodS U g S A c) :
    ¬ isMin U (A + S - 1) := by
  intro h
  have e : U (A + S - 1 + 1) = U (A + S) := congrArg U (by omega)
  have := h.2; have := hb.anchorR
  have := hb.interior (A + S - 1) (by have := hb.span; omega) (by omega); omega

theorem GoodS.isMin_left {g S : Nat} {A c : Int} (hb : GoodS U g S A c) (hguard : U A < U (A - 1)) :
    isMin U A :=
  ⟨hguard, by have := hb.interior (A + 1) (by omega) (by have := hb.span; omega)
              have := hb.anchorL; omega⟩

/-- Single interior root at `A+g`: interior roots are exactly `{A+g}`. -/
theorem GoodS.single_root {g S : Nat} {A c : Int} (hb : GoodS U g S A c)
    (hleast : ∀ k, A < k → k < A + S → k ≠ A + g → U (A + g) < U k)
    (hinc : ∀ k, A < k → k + 1 < A + g → U k < U (k + 1))
    (hdec : ∀ k, A + g < k → k + 1 < A + S → U (k + 1) < U k) :
    ∀ k, A < k → k < A + S → (isMin U k ↔ k = A + g) := by
  have g2 := hb.g2; have sp := hb.span
  intro k hk1 hk2
  constructor
  · intro h
    by_cases hk : k = A + g
    · exact hk
    · exfalso
      by_cases hlt : k < A + g
      · by_cases hk1' : k = A + 1
        · subst hk1'; exact hb.first_not_min h
        · have := hinc (k - 1) (by omega) (by omega)
          have e : U (k - 1 + 1) = U k := congrArg U (by omega)
          have := h.1; omega
      · by_cases hkl : k = A + S - 1
        · subst hkl; exact hb.last_not_min h
        · have := hdec k (by omega) (by omega)
          have := h.2; omega
  · intro hk; subst hk
    exact ⟨hleast (A + g - 1) (by omega) (by omega) (by omega),
           hleast (A + g + 1) (by omega) (by omega) (by omega)⟩

/-- With span `S = 2g+1` and the single-root pattern, exactly one gap of length `g`
lies in `[A, A+S]`, namely the one starting at `A`  (`H = 1`). -/
theorem GoodS.single_root_H_one {g : Nat} {A c : Int} (hb : GoodS U g (2 * g + 1) A c)
    (hguard : U A < U (A - 1))
    (hleast : ∀ k, A < k → k < A + (2 * g + 1 : Nat) → k ≠ A + g → U (A + g) < U k)
    (hinc : ∀ k, A < k → k + 1 < A + g → U k < U (k + 1))
    (hdec : ∀ k, A + g < k → k + 1 < A + (2 * g + 1 : Nat) → U (k + 1) < U k) :
    ∀ j, A ≤ j → j + g ≤ A + (2 * g + 1 : Nat) → (gapAt U g j ↔ j = A) := by
  have g2 := hb.g2
  have hr := hb.single_root hleast hinc hdec
  have hmid : isMin U (A + g) := (hr (A + g) (by omega) (by omega)).2 rfl
  intro j hj1 hj2
  constructor
  · intro hgap
    by_cases hjA : j = A
    · exact hjA
    · exfalso
      have hjg : j = A + g := (hr j (by omega) (by omega)).1 hgap.1
      -- then j + g = A + 2g is an interior site of the span-(2g+1) block, not a root
      have := (hr (j + g) (by omega) (by omega)).1 hgap.2.1
      omega
  · intro hjA; subst hjA
    refine ⟨hb.isMin_left hguard, hmid, ?_⟩
    intro t t0 tg ht
    have := (hr (j + t) (by omega) (by omega)).1 ht; omega

/-- With span `S = 2g+1` and increasing interior, no gap of length `g` (`H = 0`). -/
theorem GoodS.increasing_H_zero {g : Nat} {A c : Int} (hb : GoodS U g (2 * g + 1) A c)
    (hinc : ∀ k, A < k → k + 1 < A + (2 * g + 1 : Nat) → U k < U (k + 1)) :
    ∀ j, A ≤ j → j + g ≤ A + (2 * g + 1 : Nat) → ¬ gapAt U g j := by
  have g2 := hb.g2
  have hno : ∀ k, A < k → k < A + (2 * g + 1 : Nat) → ¬ isMin U k := by
    intro k hk1 hk2 h
    by_cases hk : k = A + 1
    · subst hk; exact hb.first_not_min h
    · have := hinc (k - 1) (by omega) (by omega)
      have e : U (k - 1 + 1) = U k := congrArg U (by omega)
      have := h.1; omega
  intro j hj1 hj2 hgap
  by_cases hjA : j = A
  · subst hjA; exact hno (j + g) (by omega) (by omega) hgap.2.1
  · exact hno j (by omega) (by omega) hgap.1

/-! ### Lemma 2.3(b) in full: which products `Y_0^{(g)} Y_h^{(g')}` can be nonzero -/

/-- If a gap of length `g` starts at `j` and a gap of length `g'` starts at `j+h`, then
`h ∈ {g, g+2, -g', -g'-2}`, or `h = 0` and `g = g'`, or the two windows are disjoint
(`h < -g'-2` or `h > g+2`).  This is Lemma 2.3(b) of the paper, for arbitrary `g, g' ≥ 2`. -/
theorem gap_product_zero (g g' : Nat) (hg : 2 ≤ g) (hg' : 2 ≤ g') (j h : Int)
    (h1 : gapAt U g j) (h2 : gapAt U g' (j + h)) :
    h = g ∨ h = g + 2 ∨ h = -(g' : Int) ∨ h = -(g' : Int) - 2 ∨ (h = 0 ∧ g = g') ∨
      h < -(g' : Int) - 2 ∨ (g : Int) + 2 < h := by
  by_cases c1 : (g : Int) + 2 < h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c1)))))
  by_cases c2 : h < -(g' : Int) - 2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c2)))))
  by_cases c3 : h = g
  · exact Or.inl c3
  by_cases c4 : h = g + 2
  · exact Or.inr (Or.inl c4)
  by_cases c5 : h = -(g' : Int)
  · exact Or.inr (Or.inr (Or.inl c5))
  by_cases c6 : h = -(g' : Int) - 2
  · exact Or.inr (Or.inr (Or.inr (Or.inl c6)))
  by_cases c0 : h = 0 ∧ g = g'
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c0))))
  exfalso
  by_cases c7 : h = g + 1
  · -- valleys at j+g and j+g+1 would be adjacent
    have e : j + h = (j + g) + 1 := by omega
    have a := h2.1
    rw [e] at a
    exact not_isMin_succ U _ h1.2.1 a
  by_cases c8 : h = -(g' : Int) - 1
  · -- valleys at j-1 and j would be adjacent
    have e : j + h + (g' : Int) = j - 1 := by omega
    have a := h2.2.1
    rw [e] at a
    have b := not_isMin_succ U (j - 1) a
    have e2 : j - 1 + 1 = j := by omega
    rw [e2] at b
    exact b h1.1
  by_cases c9 : 0 < h
  · -- 0 < h < g: the valley at j+h lies strictly inside the first gap
    exact no_root_inside_gap U g j (j + h) h2.1 h1 (by omega) (by omega)
  by_cases c10 : h < 0
  · -- -g' < h < 0: the valley at j lies strictly inside the second gap
    exact no_root_inside_gap U g' (j + h) j h1.1 h2 (by omega) (by omega)
  -- h = 0 and g ≠ g'
  have h0 : h = 0 := by omega
  subst h0
  rw [Int.add_zero] at h2
  by_cases lt : g < g'
  · exact no_root_inside_gap U g' j (j + g) h1.2.1 h2 (by omega) (by omega)
  · have lt' : g' < g := by omega
    exact no_root_inside_gap U g j (j + g') h2.2.1 h1 (by omega) (by omega)

end LM
