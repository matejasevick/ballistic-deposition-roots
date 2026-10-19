/-!
# Ballistic deposition: roots are exactly the "first-arrival local minima"

Deterministic core of the Poissonization step in Task 1.
Sites form any type `α` with a left and a right neighbour map (on the cycle `Fin K`,
`K ≥ 2`, these are `x ↦ x-1` and `x ↦ x+1` mod `K`).  A particle dropped at `j`
lands at height `1 + max (h (left j)) (max (h j) (h (right j)))`.

Main theorem (`isRoot_iff`): for every finite drop sequence `seq`, site `x` ever
receives a particle at height one iff the first occurrence of `x` in `seq` precedes
the first occurrences of both neighbours (an absent site has index `seq.length`).
No Mathlib is used; this file checks with plain Lean 4.
-/

set_option linter.unusedSectionVars false

namespace BD

variable {α : Type} [DecidableEq α]

/-- Index of the first occurrence of `a` in a list (`= length` if `a` is absent). -/
def idx (a : α) : List α → Nat
  | [] => 0
  | b :: l => if b = a then 0 else idx a l + 1

theorem idx_le_length (a : α) : ∀ l : List α, idx a l ≤ l.length
  | [] => by simp [idx]
  | b :: l => by
    have := idx_le_length a l
    simp only [idx, List.length_cons]; split <;> omega

theorem mem_of_idx_lt (a : α) : ∀ l : List α, idx a l < l.length → a ∈ l
  | [] => by simp [idx]
  | b :: l => by
    intro h
    simp only [idx, List.length_cons] at h
    by_cases hb : b = a
    · subst hb; exact List.mem_cons_self _ _
    · rw [if_neg hb] at h
      exact List.mem_cons_of_mem _ (mem_of_idx_lt a l (by omega))

/-- Neighbourhood structure: each site has a left and a right neighbour distinct from it. -/
structure Nbhd (α : Type) where
  left : α → α
  right : α → α
  left_ne : ∀ x, left x ≠ x
  right_ne : ∀ x, right x ≠ x

variable (N : Nbhd α)

/-- Height of the particle that lands when dropping at `j` on profile `h`. -/
def newHeight (h : α → Nat) (j : α) : Nat :=
  1 + max (h (N.left j)) (max (h j) (h (N.right j)))

/-- Profile after dropping one particle at `j`. -/
def step (h : α → Nat) (j : α) : α → Nat :=
  fun x => if x = j then newHeight N h j else h x

/-- `hitsOne h js x`: starting from profile `h` and dropping at the sites of `js` in order,
site `x` at some moment receives a particle at height one. -/
def hitsOne : (α → Nat) → List α → α → Prop
  | _, [], _ => False
  | h, j :: js, x => (j = x ∧ newHeight N h j = 1) ∨ hitsOne (step N h j) js x

/-- `x` is a root of the deposition driven by `seq` (from the flat initial profile). -/
def isRoot (seq : List α) (x : α) : Prop := hitsOne N (fun _ => 0) seq x

theorem newHeight_eq_one (h : α → Nat) (j : α) :
    newHeight N h j = 1 ↔ h (N.left j) = 0 ∧ h j = 0 ∧ h (N.right j) = 0 := by
  unfold newHeight
  simp only [Nat.max_def]
  split <;> split <;> omega

theorem newHeight_pos (h : α → Nat) (j : α) : newHeight N h j ≠ 0 := by
  unfold newHeight; omega

/-- Invariant form: if the profile `h` vanishes exactly off the visited set `V`, then `x`
later receives a height-one particle iff `x` and both neighbours are unvisited and the
first future visit of `x` precedes the first future visits of both neighbours. -/
theorem hitsOne_iff (js : List α) :
    ∀ (V : α → Prop) (h : α → Nat), (∀ y, h y = 0 ↔ ¬ V y) → ∀ x : α,
    (hitsOne N h js x ↔
      (¬ V x ∧ ¬ V (N.left x) ∧ ¬ V (N.right x) ∧
        idx x js < idx (N.left x) js ∧ idx x js < idx (N.right x) js)) := by
  induction js with
  | nil =>
    intro V h _ x
    simp [hitsOne, idx]
  | cons j js ih =>
    intro V h hV x
    have hV' : ∀ y, step N h j y = 0 ↔ ¬ (V y ∨ y = j) := by
      intro y
      unfold step
      by_cases hy : y = j
      · simp only [hy, if_true]
        have := newHeight_pos N h j
        constructor
        · intro h0; exact absurd h0 this
        · intro hn; exact absurd (Or.inr trivial) hn
      · rw [if_neg hy, hV y]
        constructor
        · intro hn hor; cases hor with
          | inl hv => exact hn hv
          | inr he => exact hy he
        · intro hn hv; exact hn (Or.inl hv)
    have ihx := ih (fun y => V y ∨ y = j) (step N h j) hV' x
    simp only [hitsOne]
    rw [ihx, newHeight_eq_one]
    have hl := N.left_ne x
    have hr := N.right_ne x
    by_cases hjx : j = x
    · subst hjx
      have e1 : (j = N.left j) = False := propext ⟨fun e => hl e.symm, False.elim⟩
      have e2 : (j = N.right j) = False := propext ⟨fun e => hr e.symm, False.elim⟩
      simp only [idx, if_true, e1, e2, if_false, hV]
      constructor
      · intro hh
        cases hh with
        | inl h1 => exact ⟨h1.2.2.1, h1.2.1, h1.2.2.2, by omega, by omega⟩
        | inr h2 => exact absurd (Or.inr trivial) h2.1
      · intro hh
        exact Or.inl ⟨trivial, hh.2.1, hh.1, hh.2.2.1⟩
    · simp only [idx, if_neg hjx]
      by_cases hjl : j = N.left x
      · simp only [hjl, if_true]
        constructor
        · intro hh
          cases hh with
          | inl h1 => exact absurd (hjl ▸ h1.1) hl
          | inr h2 => exact absurd (Or.inr trivial) h2.2.1
        · intro hh; exact absurd hh.2.2.2.1 (by omega)
      · by_cases hjr : j = N.right x
        · simp only [hjr, if_true, if_neg hjl]
          constructor
          · intro hh
            cases hh with
            | inl h1 => exact absurd (hjr ▸ h1.1) hr
            | inr h2 => exact absurd (Or.inr trivial) h2.2.2.1
          · intro hh; exact absurd hh.2.2.2.2 (by omega)
        · simp only [if_neg hjl, if_neg hjr]
          have ne1 : ¬ (N.left x = j) := fun e => hjl e.symm
          have ne2 : ¬ (N.right x = j) := fun e => hjr e.symm
          have ne0 : ¬ (x = j) := fun e => hjx e.symm
          constructor
          · intro hh
            cases hh with
            | inl h1 => exact absurd h1.1 hjx
            | inr h2 =>
              exact ⟨fun v => h2.1 (Or.inl v), fun v => h2.2.1 (Or.inl v),
                fun v => h2.2.2.1 (Or.inl v), by omega, by omega⟩
          · intro hh
            refine Or.inr ⟨?_, ?_, ?_, by omega, by omega⟩
            · intro hv; cases hv with
              | inl v => exact hh.1 v
              | inr e => exact ne0 e
            · intro hv; cases hv with
              | inl v => exact hh.2.1 v
              | inr e => exact ne1 e
            · intro hv; cases hv with
              | inl v => exact hh.2.2.1 v
              | inr e => exact ne2 e

/-- **Root characterisation.** `x` is a root iff its first arrival precedes the first
arrivals of both neighbours. -/
theorem isRoot_iff (seq : List α) (x : α) :
    isRoot N seq x ↔ idx x seq < idx (N.left x) seq ∧ idx x seq < idx (N.right x) seq := by
  unfold isRoot
  rw [hitsOne_iff N seq (fun _ => False) (fun _ => 0) (fun _ => by simp) x]
  simp

/-- A root is a site that actually receives a particle. -/
theorem mem_of_isRoot (seq : List α) (x : α) (hx : isRoot N seq x) : x ∈ seq := by
  rw [isRoot_iff] at hx
  exact mem_of_idx_lt x seq (Nat.lt_of_lt_of_le hx.1 (idx_le_length _ _))

/-- Consequence used for the Poisson-clock argument: in terms of the priorities
`U y := idx y seq` (first-arrival ranks), roots are exactly the strict local minima. -/
theorem isRoot_iff_localMin (seq : List α) (x : α) :
    isRoot N seq x ↔
      (fun y => idx y seq) x < (fun y => idx y seq) (N.left x) ∧
      (fun y => idx y seq) x < (fun y => idx y seq) (N.right x) :=
  isRoot_iff N seq x

/-! ### The cyclic strip `Fin K`, `K ≥ 2` -/

def cyc (K : Nat) (hK : 2 ≤ K) : Nbhd (Fin K) where
  left x := ⟨(x.val + K - 1) % K, Nat.mod_lt _ (by omega)⟩
  right x := ⟨(x.val + 1) % K, Nat.mod_lt _ (by omega)⟩
  left_ne x := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    have hx := x.isLt
    by_cases h0 : x.val = 0
    · rw [h0, Nat.mod_eq_of_lt (by omega)] at hv; omega
    · have e : x.val + K - 1 = (x.val - 1) + K := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hv; omega
  right_ne x := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    have hx := x.isLt
    by_cases h1 : x.val + 1 = K
    · rw [h1, Nat.mod_self] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega

/-- The theorem on the cyclic strip with `K ≥ 2` sites. -/
theorem cyc_isRoot_iff (K : Nat) (hK : 2 ≤ K) (seq : List (Fin K)) (x : Fin K) :
    isRoot (cyc K hK) seq x ↔
      idx x seq < idx ((cyc K hK).left x) seq ∧ idx x seq < idx ((cyc K hK).right x) seq :=
  isRoot_iff _ seq x

/-! ### Monotonicity of the dynamics (deterministic core of Proposition 7.4)
If one profile dominates another up to an additive constant, the domination survives any common
sequence of deposits.  Comparing the process at time `n+k` with the process restarted from the flat
profile at time `n` gives `M_{n+k} ≤ M_n + M'_k` and `L_{n+k} ≥ L_n + L'_k`. -/

/-- Run the deposition dynamics along a list of sites. -/
def run (h : α → Nat) : List α → α → Nat
  | [] => h
  | j :: js => run (step N h j) js

theorem step_shift_ge (c : Nat) (h h' : α → Nat) (hle : ∀ x, c + h' x ≤ h x) (j : α) :
    ∀ x, c + step N h' j x ≤ step N h j x := by
  intro x
  unfold step
  by_cases hx : x = j
  · simp only [hx, if_true]
    unfold newHeight
    have a := hle (N.left j); have b := hle j; have d := hle (N.right j)
    simp only [Nat.max_def]
    split <;> split <;> split <;> split <;> omega
  · simp only [hx, if_false]; exact hle x

theorem step_shift_le (c : Nat) (h h' : α → Nat) (hle : ∀ x, h x ≤ c + h' x) (j : α) :
    ∀ x, step N h j x ≤ c + step N h' j x := by
  intro x
  unfold step
  by_cases hx : x = j
  · simp only [hx, if_true]
    unfold newHeight
    have a := hle (N.left j); have b := hle j; have d := hle (N.right j)
    simp only [Nat.max_def]
    split <;> split <;> split <;> split <;> omega
  · simp only [hx, if_false]; exact hle x

theorem run_shift_ge (c : Nat) : ∀ (js : List α) (h h' : α → Nat), (∀ x, c + h' x ≤ h x) →
    ∀ x, c + run N h' js x ≤ run N h js x
  | [], _, _, hle => hle
  | j :: js, h, h', hle => run_shift_ge c js _ _ (step_shift_ge N c h h' hle j)

theorem run_shift_le (c : Nat) : ∀ (js : List α) (h h' : α → Nat), (∀ x, h x ≤ c + h' x) →
    ∀ x, run N h js x ≤ c + run N h' js x
  | [], _, _, hle => hle
  | j :: js, h, h', hle => run_shift_le c js _ _ (step_shift_le N c h h' hle j)

/-- Running from the profile reached after `w₁` and continuing with `w₂` is running `w₁ ++ w₂`. -/
theorem run_append (h : α → Nat) : ∀ (w₁ w₂ : List α), run N h (w₁ ++ w₂) = run N (run N h w₁) w₂
  | [], _ => rfl
  | j :: js, w₂ => run_append (step N h j) js w₂

/-- Sub/superadditivity in pointwise form: with `H = run 0 (w₁ ++ w₂)`, `H₁ = run 0 w₁` and
`H' = run 0 w₂` (the restarted process), any lower bound `c ≤ H₁` and upper bound `H₁ ≤ C`
give `c + H' ≤ H ≤ C + H'`. -/
theorem run_restart_bounds (w₁ w₂ : List α) (c C : Nat)
    (hc : ∀ x, c ≤ run N (fun _ => 0) w₁ x) (hC : ∀ x, run N (fun _ => 0) w₁ x ≤ C) :
    ∀ x, c + run N (fun _ => 0) w₂ x ≤ run N (fun _ => 0) (w₁ ++ w₂) x ∧
         run N (fun _ => 0) (w₁ ++ w₂) x ≤ C + run N (fun _ => 0) w₂ x := by
  intro x
  rw [run_append]
  exact ⟨run_shift_ge N c w₂ _ _ (fun y => by have := hc y; omega) x,
         run_shift_le N C w₂ _ _ (fun y => by have := hC y; omega) x⟩

-- sanity check by evaluation on a concrete run (K = 5)
def rootsDec (K : Nat) (hK : 2 ≤ K) (seq : List (Fin K)) : List (Fin K) :=
  ((List.range K).filterMap fun v => if h : v < K then some (⟨v, h⟩ : Fin K) else none).filter fun x =>
    decide (idx x seq < idx ((cyc K hK).left x) seq ∧ idx x seq < idx ((cyc K hK).right x) seq)

#eval rootsDec 5 (by decide) [2, 0, 4, 3, 1, 2, 2]   -- expected: [0, 2]

end BD
