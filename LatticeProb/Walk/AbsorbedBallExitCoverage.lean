import LatticeProb.Prob.BrownianOpenExit
import Mathlib.Tactic

/-! # Ball exits before terminal absorption -/

set_option autoImplicit false

open scoped NNReal ENNReal

namespace LatticeProb

/-- If two terminal-absorbed paths are uniformly close after an order-preserving
change of clock, an endpoint beyond a buffered ball forces both paths to exit
the ball before their respective terminal times. -/
theorem openExitTime_ball_le_terminal_of_absorbed_dist_le
    {E : Type*} [PseudoMetricSpace E] (f g : ℝ≥0 → E)
    (T U : ℝ≥0) (φ : ℝ≥0 ≃o ℝ≥0) (z : E) (r e : ℝ)
    (hclose : ∀ t, dist (f (min t T)) (g (min (φ t) U)) ≤ e)
    (hmargin : r + e ≤ dist (g U) z) :
    openExitTime (fun t (_ : Unit) => f t) (Metric.ball z r) () ≤ (T : ℝ≥0∞) ∧
    openExitTime (fun t (_ : Unit) => g t) (Metric.ball z r) () ≤ (U : ℝ≥0∞) := by
  have hT : T ≤ max T (φ.symm U) := le_max_left _ _
  have hU : U ≤ φ (max T (φ.symm U)) := by
    simp
  have hc : dist (f T) (g U) ≤ e := by
    simpa only [min_eq_right hT, min_eq_right hU] using hclose (max T (φ.symm U))
  have he : 0 ≤ e := (dist_nonneg : 0 ≤ dist (f T) (g U)).trans hc
  have hf : f T ∉ Metric.ball z r := by
    simp only [Metric.mem_ball, not_lt]
    linarith [dist_triangle (g U) (f T) z, dist_comm (g U) (f T)]
  have hg : g U ∉ Metric.ball z r := by
    simp only [Metric.mem_ball, not_lt]
    linarith
  exact ⟨openExitTime_le_of_not_mem hf, openExitTime_le_of_not_mem hg⟩

end LatticeProb
