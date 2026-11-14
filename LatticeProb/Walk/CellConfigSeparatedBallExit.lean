import LatticeProb.Walk.CellConfigExteriorExitBracket
import LatticeProb.Walk.CellConfigNearbyStoppedRepresentatives

/-! # Exit stability for close cell representatives -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- If the representatives up to the first exterior vertex are separated from
    the boundary by their maximal discrepancy, both exit times lie on the same
    holding-clock edge and the stopped interpolations are uniformly close. -/
theorem stopped_interpolatedWalk_ball_exit_le_of_separated_representatives
    (H : CellConfig) (hH : H.IsCellConfiguration)
    (p q : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (hq : ∀ K, q K ∈ (K.1 : Set Plane))
    (ω : ℕ → H.cells) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) (n : ℕ)
    (hadj : H.Adj (ω n) (ω (n + 1)))
    {r L : ℝ} (hclose : ∀ K, dist (p K) (q K) ≤ r)
    (hedge : ∀ i, dist (p (ω i)) (p (ω (i + 1))) ≤ L)
    {ε : ℝ≥0} (hε : 0 < ε) (z : Plane) (R : ℝ)
    (hin : ∀ j ≤ n, dist ((ε : ℝ) • p (ω j)) z < R - (ε : ℝ) * r)
    (hout : R + (ε : ℝ) * r ≤ dist ((ε : ℝ) • p (ω (n + 1))) z) :
    let s := continuousExitTime (Metric.ball z R) 0 (H.interpolatedWalk p ε ω)
    let u := continuousExitTime (Metric.ball z R) 0 (H.interpolatedWalk q ε ω)
    s ≠ ∞ ∧ u ≠ ∞ ∧ ∀ t : ℝ≥0,
      dist ((H.interpolatedWalk p ε ω) (min t s.toNNReal))
        ((H.interpolatedWalk q ε ω) (min t u.toNNReal)) ≤
        2 * (ε : ℝ) * L + (ε : ℝ) * r := by
  have hr : 0 ≤ r := le_trans dist_nonneg (hclose (ω 0))
  have her : 0 ≤ (ε : ℝ) * r := mul_nonneg ε.coe_nonneg hr
  have hscaled (K : H.cells) : dist ((ε : ℝ) • p K) ((ε : ℝ) • q K) ≤
      (ε : ℝ) * r := by
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ε.coe_nonneg, ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (hclose K) ε.coe_nonneg
  have hpin : ∀ j ≤ n, (ε : ℝ) • p (ω j) ∈ Metric.ball z R := by
    intro j hj
    simp only [Metric.mem_ball]
    linarith [hin j hj]
  have hqin : ∀ j ≤ n, (ε : ℝ) • q (ω j) ∈ Metric.ball z R := by
    intro j hj
    simp only [Metric.mem_ball]
    have h := dist_triangle ((ε : ℝ) • q (ω j)) ((ε : ℝ) • p (ω j)) z
    rw [dist_comm ((ε : ℝ) • q (ω j)) ((ε : ℝ) • p (ω j))] at h
    linarith [hin j hj, hscaled (ω j)]
  have hpout : (ε : ℝ) • p (ω (n + 1)) ∉ Metric.ball z R := by
    simp only [Metric.mem_ball, not_lt]
    linarith
  have hqout : (ε : ℝ) • q (ω (n + 1)) ∉ Metric.ball z R := by
    simp only [Metric.mem_ball, not_lt]
    have h := dist_triangle ((ε : ℝ) • p (ω (n + 1)))
      ((ε : ℝ) • q (ω (n + 1))) z
    linarith [hscaled (ω (n + 1))]
  obtain ⟨hs, hs₁, hs₂, _⟩ := continuousExitTime_bracket_of_first_exterior
    H hH p hp ω hpos hunb n hadj hε Metric.isOpen_ball (convex_ball z R) hpin hpout
  obtain ⟨hu, hu₁, hu₂, _⟩ := continuousExitTime_bracket_of_first_exterior
    H hH q hq ω hpos hunb n hadj hε Metric.isOpen_ball (convex_ball z R) hqin hqout
  refine ⟨hs, hu, fun t => ?_⟩
  exact dist_stopped_interpolatedWalk_le_of_nearby_edges H p q ω hpos hunb
    hclose hedge hε n n _ _ hs₁.le hs₂ hu₁.le hu₂ (by omega) (by omega) t

end LatticeProb.CellConfigInterpolation
end
