import Mathlib

/-!
# The volume of the Euclidean unit ball

`omegaD d` is the Lebesgue volume `ω_d` of the open unit ball of `ℝ^d`. A ball of volume `n` has
radius `(n / ω_d)^{1/d}`, the radius in the growth rates of A. Fey, L. Levine and Y. Peres,
*Growth rates and explosions in sandpiles*, J. Stat. Phys. 138 (2010), 143–159.
-/

namespace LatticeProb.Sandpile.FLP

open MeasureTheory

/-- The Lebesgue volume of the open unit ball of `ℝ^d`. -/
noncomputable def omegaD (d : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

/-- The volume of the unit ball is positive. -/
theorem omegaD_pos (d : ℕ) : 0 < omegaD d :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

end LatticeProb.Sandpile.FLP
