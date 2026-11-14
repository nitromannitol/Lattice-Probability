import LatticeProb.Prob.BrownianOpenExit

/-!
# Confinement up to a first exit

A continuous path starting in a closed set remains in that set up to and including its first
exit from an open subset. The initial point may lie on the boundary and the exit time may be
infinite.
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace LatticeProb

/-- A continuous path starting in `K` stays in `K` through its first exit from the open set `U`,
provided that `U ⊆ K` and `K` is closed. -/
theorem mem_closed_of_le_openExitTime {Ω E : Type*} [TopologicalSpace E]
    {B : ℝ≥0 → Ω → E} {U K : Set E} {ω : Ω}
    (hU : IsOpen U) (hK : IsClosed K) (hUK : U ⊆ K)
    (hcont : Continuous fun t : ℝ≥0 => B t ω) (hstart : B 0 ω ∈ K)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ openExitTime B U ω) : B t ω ∈ K := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact hUK (mem_of_lt_openExitTime hlt)
  · by_cases h0 : B 0 ω ∈ U
    · have hfinite : openExitTime B U ω ≠ ∞ := by rw [← heq]; exact ENNReal.coe_ne_top
      have hfront := openExitTime_mem_frontier hU hcont h0 hfinite
      have hclosed : closure U ⊆ K := closure_minimal hUK hK
      apply hclosed
      have htime : (openExitTime B U ω).toNNReal = t := by rw [← heq, ENNReal.toNNReal_coe]
      rw [← htime]
      exact frontier_subset_closure hfront
    · have hzero := openExitTime_eq_zero_of_not_mem h0
      have ht0 : t = 0 := by
        have : (t : ℝ≥0∞) = 0 := heq.trans hzero
        exact ENNReal.coe_eq_zero.mp this
      simpa only [ht0] using hstart

end LatticeProb
