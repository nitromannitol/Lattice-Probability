import LatticeProb.Prob.BrownianExitEndpointTranslation

/-! # Stopped endpoints from exterior starting points -/

set_option autoImplicit false
noncomputable section

open MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- A path started outside an open set exits at once, so its stopped endpoint
law is the Dirac measure at its starting point. -/
theorem stoppedBrownianLaw_endPoint_eq_dirac_of_not_mem {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) (hz : z ∉ U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hzero : ∀ᵐ ω ∂μ, ω 0 = 0) :
    (stoppedBrownianLaw U z μ).map BouRabeeGwynne.CurveSpace.endPoint = Measure.dirac z := by
  rw [stoppedBrownianLaw, Measure.map_map BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable
    (measurable_stoppedBrownianCurve hU z)]
  have h : (BouRabeeGwynne.CurveSpace.endPoint ∘ stoppedBrownianCurve U z) =ᵐ[μ] (fun _ => z) := by
    filter_upwards [hzero] with ω hω
    have ht : continuousExitTime U z ω = 0 :=
      continuousExitTime_eq_zero_of_not_mem (by simpa only [hω, add_zero] using hz)
    simp only [Function.comp_apply, stoppedBrownianCurve_endPoint, ht,
      ENNReal.toNNReal_zero, hω, add_zero]
  rw [Measure.map_congr h, Measure.map_const, measure_univ, one_smul]

end LatticeProb
end
