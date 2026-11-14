import LatticeProb.Walk.CellConfigExitCollar
import LatticeProb.Walk.CellConfigFiniteExit

/-! # Collar containment for stopped interpolated walks -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The collar bound includes the last jump and the path stopped at that jump,
provided at least one representative before it belongs to the set. -/
theorem stopped_interpolatedWalk_mem_cthickening (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) (U : Set Plane) (n : ℕ) (d : ℝ)
    (hin : ∀ j < n + 1, (ε : ℝ) • p (ω j) ∈ U)
    (hd : ∀ j < n + 1, Metric.diam ((ω j).1 : Set Plane) +
      Metric.diam ((ω (j + 1)).1 : Set Plane) ≤ d)
    (t : ℝ≥0) :
    H.interpolatedWalk p ε ω (min t
      ⟨(ε : ℝ) ^ 2 * H.jumpTime ω (n + 1),
        mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos (n + 1))⟩)
      ∈ Metric.cthickening ((ε : ℝ) * d) U := by
  let T : ℝ≥0 := ⟨(ε : ℝ) ^ 2 * H.jumpTime ω (n + 1),
    mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos (n + 1))⟩
  change H.interpolatedWalk p ε ω (min t T) ∈ _
  by_cases ht : t < T
  · rw [min_eq_left ht.le]
    apply interpolatedWalk_mem_cthickening_before_jump H hH p hp ω hpos hunb hadj hε U (n + 1) d hin hd t
    exact_mod_cast ht
  · rw [min_eq_right (le_of_not_gt ht)]
    change H.interpolatedWalk p ε ω ⟨_, _⟩ ∈ _
    rw [interpolatedWalk_at_jumpTime H p ω hpos hunb (n + 1) hε]
    apply Metric.mem_cthickening_of_dist_le _ ((ε : ℝ) • p (ω n)) _ U
      (hin n (Nat.lt_succ_self n))
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ε.coe_nonneg,
      ← dist_eq_norm, dist_comm]
    exact mul_le_mul_of_nonneg_left
      ((dist_representatives_le H hH p hp (hadj n) |>.trans (hd n (Nat.lt_succ_self n))))
      ε.coe_nonneg

/-- Stopping at the first exterior vertex retains the collar when the initial
representative is in the set. -/
theorem stopped_interpolatedWalk_mem_cthickening_of_exterior_hit (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) (U : Set Plane) (n : ℕ) (d : ℝ)
    (hfirst : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ∞))
    (hd : ∀ j < n + 1, Metric.diam ((ω j).1 : Set Plane) +
      Metric.diam ((ω (j + 1)).1 : Set Plane) ≤ d)
    (t : ℝ≥0) :
    H.interpolatedWalk p ε ω (min t
      ⟨(ε : ℝ) ^ 2 * H.jumpTime ω (n + 1),
        mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos (n + 1))⟩)
      ∈ Metric.cthickening ((ε : ℝ) * d) U := by
  apply stopped_interpolatedWalk_mem_cthickening H hH p hp ω hpos hunb hadj hε U n d ?_ hd t
  intro j hj
  exact not_not.mp ((hitTime_eq_coe_iff.mp hfirst).2 j hj)

end LatticeProb.CellConfigInterpolation
end
