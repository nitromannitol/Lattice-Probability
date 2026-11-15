import LatticeProb.Analysis.WedgeArcIntegral

/-! # Principal arguments of angular circle measures -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The principal argument recovers Lebesgue measure on an angular interval. -/
theorem map_arg_wedgeArcMeasure {θ : ℝ} (hθ : θ ≤ 2 * Real.pi) :
    Measure.map Complex.arg (wedgeArcMeasure θ) =
      volume.restrict (Ioc (-θ / 2) (θ / 2)) := by
  rw [wedgeArcMeasure, Measure.map_map Complex.measurable_arg (by fun_prop)]
  have heq : (Complex.arg ∘ circleMap 0 1) =ᵐ[volume.restrict (Ioc (-θ / 2) (θ / 2))] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact arg_circleMap_mem_wedge hθ hx
  rw [Measure.map_congr heq, Measure.map_id]

/-- A measure supported on the unit circle is determined by its principal argument. -/
theorem eq_wedgeArcMeasure_of_map_arg {θ : ℝ} {μ : Measure ℂ}
    (hμ : ∀ᵐ z ∂μ, ‖z‖ = 1)
    (harg : Measure.map Complex.arg μ = volume.restrict (Ioc (-θ / 2) (θ / 2))) :
    μ = wedgeArcMeasure θ := by
  have hrec : (circleMap 0 1 ∘ Complex.arg) =ᵐ[μ] id := by
    filter_upwards [hμ] with z hz
    change circleMap 0 1 z.arg = z
    simpa only [circleMap_zero, Complex.ofReal_one, one_mul, hz] using
      (Complex.norm_mul_exp_arg_mul_I z)
  calc
    μ = Measure.map (circleMap 0 1 ∘ Complex.arg) μ := by
      rw [Measure.map_congr hrec, Measure.map_id]
    _ = Measure.map (circleMap 0 1) (Measure.map Complex.arg μ) := by
      rw [Measure.map_map (by fun_prop) Complex.measurable_arg]
    _ = wedgeArcMeasure θ := by rw [harg, wedgeArcMeasure]

end LatticeProb
