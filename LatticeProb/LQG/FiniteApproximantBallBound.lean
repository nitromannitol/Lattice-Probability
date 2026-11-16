import LatticeProb.LQG.FiniteApproximantCompactBound
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Ball bounds for finitely many LQG approximants -/

open MeasureTheory Set

namespace LatticeProb.LQG

/-- On a bounded set of centers, finitely many continuous approximant densities
have a common quadratic upper bound for all balls of radius at most one. -/
theorem exists_finite_lqgApprox_ball_le
    (γ : ℝ) (h : ℝ → ℂ → ℝ) (ε : ℕ → ℝ) (N : ℕ)
    (hc : ∀ k < N, Continuous (h (ε k))) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ∀ k < N, lqgApprox γ h (ε k) (Metric.ball z r) ≤ ENNReal.ofReal (C * r ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := exists_finite_lqgApprox_le_volume γ h ε N hc
    (Metric.closedBall (0 : ℂ) (R + 1)) (isCompact_closedBall _ _)
  refine ⟨A * Real.pi, mul_pos hA Real.pi_pos, ?_⟩
  intro z hz r hr hr1 k hk
  have hsub : Metric.ball z r ⊆ Metric.closedBall (0 : ℂ) (R + 1) := by
    apply Set.Subset.trans (Metric.ball_subset_ball' ?_) Metric.ball_subset_closedBall
    simpa only [dist_zero_right, add_comm] using add_le_add hr1 hz
  have hv : volume (Metric.ball z r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  calc
    lqgApprox γ h (ε k) (Metric.ball z r) ≤ ENNReal.ofReal A * volume (Metric.ball z r) :=
      hbound k hk _ Metric.isOpen_ball.measurableSet hsub
    _ = ENNReal.ofReal ((A * Real.pi) * r ^ 2) := by
      rw [hv, ← ENNReal.ofReal_mul hA.le]
      congr 1
      ring

end LatticeProb.LQG
