import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # Hausdorff dimension of sets of time pairs -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- The dimension of a set of time pairs is the supremum of the dimensions of
its restrictions where the first coordinate is bounded below and the second
is bounded above by increasing cutoffs. -/
theorem dimH_timePair_eq_iSup_interval (S : Set (ℝ × ℝ)) :
    dimH S = ⨆ n : ℕ, dimH {z : ℝ × ℝ | z ∈ S ∧ -(n : ℝ) < z.1 ∧ z.2 < n} := by
  have hS : S = ⋃ n : ℕ, {z : ℝ × ℝ | z ∈ S ∧ -(n : ℝ) < z.1 ∧ z.2 < n} := by
    ext z
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_gt (max (-z.1) z.2)
      exact ⟨n, hz, by linarith [le_max_left (-z.1) z.2],
        lt_of_le_of_lt (le_max_right (-z.1) z.2) hn⟩
    · rintro ⟨_, hz, _, _⟩
      exact hz
  calc
    dimH S = dimH (⋃ n : ℕ, {z : ℝ × ℝ | z ∈ S ∧ -(n : ℝ) < z.1 ∧ z.2 < n}) := congrArg dimH hS
    _ = _ := dimH_iUnion _

/-- A uniform dimension bound on these restrictions holds globally. -/
theorem dimH_timePair_le_of_interval (S : Set (ℝ × ℝ)) (d : ℝ≥0∞)
    (h : ∀ n : ℕ, dimH {z : ℝ × ℝ | z ∈ S ∧ -(n : ℝ) < z.1 ∧ z.2 < n} ≤ d) :
    dimH S ≤ d := by
  rw [dimH_timePair_eq_iSup_interval]
  exact iSup_le h

end LatticeProb
