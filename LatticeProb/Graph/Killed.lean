/-
The divisible-sandpile odometer of the walk killed off a set, and its
optimal-stopping representation.

The localized odometer of a set `D` is the value of the same optimal-stopping
problem as the odometer, but with the scenery summed only while the trajectory
has stayed inside `D`.  Everything here is written on the finite-horizon walk
average `walkExp`, so no measure enters; the bridge to path space is the
library's `walkAverageIsIntegral`, exactly as for the unkilled problem.

The natural route through a graph with the complement of `D` made a set of
sinks is not available: a sink is an isolated vertex, its degree is zero, and
the whole walk vocabulary divides by the degree.  What replaces it is the
observation that the killed payoff has the SAME first-step decomposition as the
payoff, with one extra factor: prepending a vertex `x` off `D` annihilates it,
and prepending a vertex inside `D` adds the scenery at `x` and leaves the
killed payoff of the remaining trajectory.  So the dynamic programming
induction of `LatticeProb.Graph.odometer_isLUB` goes through verbatim, and the
resulting recursion carries an indicator.

Connectedness is not used; the hypothesis is the positivity of the degree,
which is what the averages need and is what an infinite connected graph
provides.
-/
import LatticeProb.Graph.WalkLemmas

namespace LatticeProb.Graph

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The walk average of a constant, without connectedness -/

theorem walkExp_zero (n : ℕ) (x : V) : walkExp G n x (fun _ => (0 : ℝ)) = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [walkExp_succ]; simp [ih]

theorem walkExp_const' (hdeg : ∀ v : V, 0 < G.degree v) (n : ℕ) (x : V) (c : ℝ) :
    walkExp G n x (fun _ => c) = c := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hd : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdeg x).ne'
      rw [walkExp_succ]
      simp only [ih]
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
      field_simp

/-! ### The killed payoff -/

/-- `S_n^D = ∑_{k<n} 1{X_0,…,X_k ∈ D} ξ(X_k)/deg(X_k)`, the payoff of the walk
killed on leaving `D`. -/
noncomputable def killedPayoff (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (D : Set V)
    (n : ℕ) (X : ℕ → V) : ℝ :=
  ∑ k ∈ Finset.range n, if ∀ i ≤ k, X i ∈ D then ξ (X k) / G.degree (X k) else 0

@[simp] theorem killedPayoff_zero (ξ : V → ℝ) (D : Set V) (X : ℕ → V) :
    killedPayoff G ξ D 0 X = 0 := rfl

/-- Prepending a vertex off `D` annihilates the killed payoff. -/
theorem killedPayoff_of_notMem {ξ : V → ℝ} {D : Set V} {X : ℕ → V} (h : X 0 ∉ D) (n : ℕ) :
    killedPayoff G ξ D n X = 0 := by
  classical
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [if_neg]
  intro hk
  exact h (hk 0 (Nat.zero_le k))

/-- **The first-step decomposition of the killed payoff.** -/
theorem killedPayoff_cons (ξ : V → ℝ) (D : Set V) (m : ℕ) (x : V) (X : ℕ → V) :
    killedPayoff G ξ D (m + 1) (cons x X)
      = if x ∈ D then ξ x / G.degree x + killedPayoff G ξ D m X else 0 := by
  classical
  by_cases hx : x ∈ D
  · rw [if_pos hx, killedPayoff, Finset.sum_range_succ']
    have h0 : (if ∀ i ≤ 0, cons x X i ∈ D then ξ (cons x X 0) / G.degree (cons x X 0) else 0)
        = ξ x / G.degree x := by
      rw [if_pos]
      · rfl
      · intro i hi
        rw [Nat.le_zero.mp hi]
        exact hx
    rw [h0, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hiff : (∀ i ≤ k + 1, cons x X i ∈ D) ↔ (∀ i ≤ k, X i ∈ D) := by
      constructor
      · intro h i hi
        exact h (i + 1) (by omega)
      · intro h i hi
        match i with
        | 0 => exact hx
        | j + 1 => exact h j (by omega)
    by_cases hk : ∀ i ≤ k, X i ∈ D
    · rw [if_pos (hiff.mpr hk), if_pos hk]; rfl
    · rw [if_neg (fun h => hk (hiff.mp h)), if_neg hk]
  · rw [if_neg hx]
    exact killedPayoff_of_notMem (by simpa using hx) _

/-! ### The killed odometer and its stopping values -/

/-- The localized odometer: `w_0 = 0` and
`w_{n+1}(x) = 1_D(x) (ξ(x)/deg(x) + P w_n(x))⁺`. -/
noncomputable def killedOdometer (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ)
    (D : Set V) : ℕ → V → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      if x ∈ D then max 0 (ξ x / G.degree x + walkOp G (killedOdometer G ξ D n) x) else 0

/-- The set of expected killed payoffs over stopping times bounded by `n`. -/
noncomputable def killedStopValues (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ)
    (D : Set V) (n : ℕ) (x : V) : Set ℝ :=
  {a | ∃ τ : (ℕ → V) → ℕ, IsStopping τ ∧ (∀ X, τ X ≤ n) ∧
    a = walkExp G n x (fun X => killedPayoff G ξ D (τ X) X)}

theorem killedOdometer_nonneg (ξ : V → ℝ) (D : Set V) (n : ℕ) (x : V) :
    0 ≤ killedOdometer G ξ D n x := by
  classical
  cases n with
  | zero => exact le_rfl
  | succ n =>
      show 0 ≤ (if x ∈ D then
        max 0 (ξ x / G.degree x + walkOp G (killedOdometer G ξ D n) x) else 0)
      split_ifs
      · exact le_max_left _ _
      · exact le_rfl

theorem zero_mem_killedStopValues (ξ : V → ℝ) (D : Set V) (n : ℕ) (x : V) :
    (0 : ℝ) ∈ killedStopValues G ξ D n x := by
  refine ⟨fun _ => 0, fun _ _ _ _ h => h, fun _ => Nat.zero_le _, ?_⟩
  rw [show (fun X : ℕ → V => killedPayoff G ξ D 0 X) = (fun _ => (0 : ℝ)) from rfl,
    walkExp_zero]

theorem killedStopValues_of_notMem (ξ : V → ℝ) {D : Set V} {x : V} (hx : x ∉ D) (n : ℕ) :
    killedStopValues G ξ D n x = {(0 : ℝ)} := by
  ext a
  constructor
  · rintro ⟨τ, -, -, rfl⟩
    have : walkExp G n x (fun X => killedPayoff G ξ D (τ X) X)
        = walkExp G n x (fun _ => (0 : ℝ)) :=
      walkExp_congr fun X hX => killedPayoff_of_notMem (by rw [hX]; exact hx) _
    rw [this, walkExp_zero]
    rfl
  · rintro rfl
    exact zero_mem_killedStopValues ξ D n x

/-! ### The first-step decomposition of the killed walk average -/

theorem walkExp_killedPayoff_succ (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) {D : Set V}
    (n : ℕ) {x : V} (hx : x ∈ D) {τ : (ℕ → V) → ℕ}
    (h0 : ∀ X : ℕ → V, X 0 = x → τ X ≠ 0) :
    walkExp G (n + 1) x (fun X => killedPayoff G ξ D (τ X) X)
      = ξ x / G.degree x
        + walkOp G (fun y => walkExp G n y
            (fun X' => killedPayoff G ξ D (τ (cons x X') - 1) X')) x := by
  classical
  rw [walkExp_succ]
  have key : ∀ y ∈ G.neighborFinset x,
      walkExp G n y (fun X' => killedPayoff G ξ D (τ (cons x X')) (cons x X'))
        = ξ x / G.degree x
          + walkExp G n y (fun X' => killedPayoff G ξ D (τ (cons x X') - 1) X') := by
    intro y _
    have hcong : walkExp G n y (fun X' => killedPayoff G ξ D (τ (cons x X')) (cons x X'))
        = walkExp G n y (fun X' =>
            ξ x / G.degree x + killedPayoff G ξ D (τ (cons x X') - 1) X') := by
      refine walkExp_congr fun X' _ => ?_
      have hne : τ (cons x X') ≠ 0 := h0 _ rfl
      obtain ⟨m, hm⟩ : ∃ m, τ (cons x X') = m + 1 := ⟨τ (cons x X') - 1, by omega⟩
      rw [hm, killedPayoff_cons, if_pos hx, Nat.add_sub_cancel]
    rw [hcong, walkExp_add, walkExp_const' hdeg]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, add_div, walkOp]
  have hd : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdeg x).ne'
  congr 1
  field_simp

/-! ### The optimal-stopping representation of the killed odometer -/

/-- **The killed odometer bounds every bounded stopping rule for the killed
payoff, and is the value of one.**  This is the dynamic programming induction of
`LatticeProb.Graph.odometer_isLUB` with the killed payoff in place of the
payoff; the extra indicator is carried by `killedPayoff_cons`. -/
theorem killedOdometer_isLUB (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (D : Set V) :
    ∀ (n : ℕ) (x : V),
      (∀ a ∈ killedStopValues G ξ D n x, a ≤ killedOdometer G ξ D n x) ∧
        killedOdometer G ξ D n x ∈ killedStopValues G ξ D n x := by
  classical
  intro n
  induction n with
  | zero =>
      intro x
      refine ⟨?_, ?_⟩
      · rintro a ⟨τ, -, hle, rfl⟩
        have hz : walkExp G 0 x (fun X => killedPayoff G ξ D (τ X) X)
            = walkExp G 0 x (fun _ => (0 : ℝ)) := by
          refine walkExp_congr fun X _ => ?_
          rw [Nat.le_zero.mp (hle X)]
          rfl
        rw [hz, walkExp_zero]
        exact le_rfl
      · exact zero_mem_killedStopValues ξ D 0 x
  | succ n ih =>
      intro x
      by_cases hx : x ∈ D
      · have hrec : killedOdometer G ξ D (n + 1) x
            = max 0 (ξ x / G.degree x + walkOp G (killedOdometer G ξ D n) x) := by
          show (if x ∈ D then
            max 0 (ξ x / G.degree x + walkOp G (killedOdometer G ξ D n) x) else 0) = _
          rw [if_pos hx]
        constructor
        · rintro a ⟨τ, hτ, hle, rfl⟩
          by_cases h0 : τ (fun _ => x) = 0
          · have hz : walkExp G (n + 1) x (fun X => killedPayoff G ξ D (τ X) X)
                = walkExp G (n + 1) x (fun _ => (0 : ℝ)) := by
              refine walkExp_congr fun X hX => ?_
              rw [stopping_of_zero hτ hX h0]
              rfl
            rw [hz, walkExp_zero]
            exact killedOdometer_nonneg ξ D (n + 1) x
          · have hne : ∀ X : ℕ → V, X 0 = x → τ X ≠ 0 := fun X hX =>
              stopping_ne_zero hτ hX h0
            rw [walkExp_killedPayoff_succ hdeg ξ n hx hne]
            have hbound : ∀ y : V,
                walkExp G n y (fun X' => killedPayoff G ξ D (τ (cons x X') - 1) X')
                  ≤ killedOdometer G ξ D n y := by
              intro y
              refine (ih y).1 _ ⟨fun X' => τ (cons x X') - 1,
                isStopping_shift hτ x hne, fun X' => ?_, rfl⟩
              show τ (cons x X') - 1 ≤ n
              have := hle (cons x X')
              omega
            have hmono := walkOp_mono (G := G) hbound x
            rw [hrec]
            refine le_trans ?_ (le_max_right _ _)
            linarith
        · by_cases hpos : 0 < ξ x / G.degree x + walkOp G (killedOdometer G ξ D n) x
          · choose τ hτ hτle hτval using fun y => (ih y).2
            refine ⟨fun X => 1 + τ (X 1) (shift X), isStopping_prepend hτ, fun X => ?_, ?_⟩
            · show 1 + τ (X 1) (shift X) ≤ n + 1
              have := hτle (X 1) (shift X)
              omega
            · have hne : ∀ X : ℕ → V, X 0 = x → (1 + τ (X 1) (shift X)) ≠ 0 := by
                intro X _; omega
              rw [walkExp_killedPayoff_succ hdeg ξ n hx hne]
              have hy : ∀ y ∈ G.neighborFinset x,
                  walkExp G n y (fun X' => killedPayoff G ξ D
                      ((1 + τ ((cons x X') 1) (shift (cons x X'))) - 1) X')
                    = killedOdometer G ξ D n y := by
                intro y _
                rw [show walkExp G n y (fun X' => killedPayoff G ξ D
                      ((1 + τ ((cons x X') 1) (shift (cons x X'))) - 1) X')
                    = walkExp G n y (fun X' => killedPayoff G ξ D (τ y X') X') from
                  walkExp_congr (by
                    intro X' hX'
                    simp only [cons_succ, shift_cons, Nat.add_sub_cancel_left, hX'])]
                exact (hτval y).symm
              rw [show walkOp G (fun y => walkExp G n y (fun X' => killedPayoff G ξ D
                    ((1 + τ ((cons x X') 1) (shift (cons x X'))) - 1) X')) x
                  = walkOp G (killedOdometer G ξ D n) x from by
                simp only [walkOp]
                rw [Finset.sum_congr rfl hy]]
              rw [hrec, max_eq_right hpos.le]
          · have hzero : killedOdometer G ξ D (n + 1) x = 0 := by
              rw [hrec, max_eq_left (by linarith [not_lt.mp hpos])]
            rw [hzero]
            exact zero_mem_killedStopValues ξ D (n + 1) x
      · have hzero : killedOdometer G ξ D (n + 1) x = 0 := by
          show (if x ∈ D then
            max 0 (ξ x / G.degree x + walkOp G (killedOdometer G ξ D n) x) else 0) = 0
          rw [if_neg hx]
        rw [hzero, killedStopValues_of_notMem ξ hx]
        exact ⟨fun a ha => le_of_eq ha, rfl⟩

/-- The killed odometer is the supremum of the killed stopping values. -/
theorem isLUB_killedOdometer (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (D : Set V)
    (n : ℕ) (x : V) :
    IsLUB (killedStopValues G ξ D n x) (killedOdometer G ξ D n x) :=
  ⟨fun _ ha => (killedOdometer_isLUB hdeg ξ D n x).1 _ ha,
    fun _ hb => hb (killedOdometer_isLUB hdeg ξ D n x).2⟩

/-- **The one-step recursion for the localized odometer**, as a statement about
the supremum of the killed stopping values. -/
theorem sSup_killedStopValues (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (D : Set V)
    (n : ℕ) (x : V) :
    sSup (killedStopValues G ξ D n x) = killedOdometer G ξ D n x :=
  (isLUB_killedOdometer hdeg ξ D n x).csSup_eq
    ⟨0, zero_mem_killedStopValues ξ D n x⟩

theorem killedOdometer_succ_of_mem (ξ : V → ℝ) {D : Set V} {x : V} (hx : x ∈ D) (n : ℕ) :
    killedOdometer G ξ D (n + 1) x
      = max 0 (ξ x / G.degree x + walkOp G (killedOdometer G ξ D n) x) := by
  classical
  show (if x ∈ D then
    max 0 (ξ x / G.degree x + walkOp G (killedOdometer G ξ D n) x) else 0) = _
  rw [if_pos hx]

theorem killedOdometer_of_notMem (ξ : V → ℝ) {D : Set V} {x : V} (hx : x ∉ D) (n : ℕ) :
    killedOdometer G ξ D n x = 0 := by
  classical
  cases n with
  | zero => rfl
  | succ n =>
      show (if x ∈ D then
        max 0 (ξ x / G.degree x + walkOp G (killedOdometer G ξ D n) x) else 0) = 0
      rw [if_neg hx]

end LatticeProb.Graph
