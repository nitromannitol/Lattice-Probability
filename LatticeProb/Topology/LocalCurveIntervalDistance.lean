import LatticeProb.Topology.IntervalReparamEDist
import LatticeProb.Analysis.ExponentialWeightedSelection

/-!
# Local distance from interval reparametrization

Integrate the truncated interval distance over radii greater than one. The clock can take
infinite values. The triangle inequality requires a measurable comparison integrand.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LatticeProb.LocalCurveIntervalDistance

open IntervalReparamEDist

variable {E : Type*} [PseudoEMetricSpace E]

/-- The exponentially weighted local interval distance for a path-dependent clock. -/
noncomputable def localEDist (clock : (ℝ≥0 → E) → ℝ → ℝ≥0∞)
    (f g : ℝ≥0 → E) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-r)) *
    min 1 (intervalEDist f g (clock f r) (clock g r))

@[simp] theorem localEDist_self (clock : (ℝ≥0 → E) → ℝ → ℝ≥0∞)
    (f : ℝ≥0 → E) : localEDist clock f f = 0 := by
  simp [localEDist]

theorem localEDist_comm (clock : (ℝ≥0 → E) → ℝ → ℝ≥0∞)
    (f g : ℝ≥0 → E) : localEDist clock f g = localEDist clock g f := by
  simp only [localEDist, intervalEDist_comm f g]

private theorem min_one_add_le (x y : ℝ≥0∞) : min 1 (x + y) ≤ min 1 x + min 1 y := by
  by_cases hx : 1 ≤ x
  · rw [min_eq_left hx]
    exact (min_le_left _ _).trans (le_add_right le_rfl)
  by_cases hy : 1 ≤ y
  · rw [min_eq_left hy]
    exact (min_le_left _ _).trans (le_add_left le_rfl)
  · rw [min_eq_right (le_of_not_ge hx), min_eq_right (le_of_not_ge hy)]
    exact min_le_right _ _

/-- Triangle inequality when one of the weighted comparison integrands is almost everywhere
measurable on the integration domain. -/
theorem localEDist_triangle (clock : (ℝ≥0 → E) → ℝ → ℝ≥0∞)
    (f g h : ℝ≥0 → E)
    (hfg : AEMeasurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r)) *
      min 1 (intervalEDist f g (clock f r) (clock g r))) (volume.restrict (Ioi 1))) :
    localEDist clock f h ≤ localEDist clock f g + localEDist clock g h := by
  unfold localEDist
  calc
    _ ≤ ∫⁻ r in Ioi (1 : ℝ),
        (ENNReal.ofReal (Real.exp (-r)) * min 1 (intervalEDist f g (clock f r) (clock g r)) +
         ENNReal.ofReal (Real.exp (-r)) * min 1 (intervalEDist g h (clock g r) (clock h r))) := by
      apply lintegral_mono
      intro r
      dsimp only
      rw [← mul_add]
      exact mul_le_mul' le_rfl ((min_le_min_left _ (intervalEDist_triangle f g h _ _ _)).trans
        (min_one_add_le _ _))
    _ = _ := lintegral_add_left' hfg _

/-- A small local distance gives a radius in the prescribed interval at which the interval
reparametrization distance is small. -/
theorem exists_intervalEDist_lt_of_localEDist_lt
    (clock : (ℝ≥0 → E) → ℝ → ℝ≥0∞) (f g : ℝ≥0 → E) {a b s : ℝ}
    (ha : 1 ≤ a) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : localEDist clock f g < ENNReal.ofReal (Real.exp (-b) * s * (b - a))) :
    ∃ r ∈ Ioo a b, intervalEDist f g (clock f r) (clock g r) < ENNReal.ofReal s :=
  exists_lt_of_exp_weighted_lintegral_lt ha hs0 hs1 h

end LatticeProb.LocalCurveIntervalDistance
