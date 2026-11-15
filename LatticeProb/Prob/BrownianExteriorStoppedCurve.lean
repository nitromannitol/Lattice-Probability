import LatticeProb.Prob.BrownianExitEndpointTranslation

/-! # Stopped curve laws from exterior starting points -/

set_option autoImplicit false
noncomputable section

open MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- A path started outside a set has the constant stopped curve. -/
theorem stoppedBrownianLaw_eq_dirac_of_not_mem {d : ℕ}
    {U : Set (Euc d)} (z : Euc d) (hz : z ∉ U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hzero : ∀ᵐ ω ∂μ, ω 0 = 0) :
    stoppedBrownianLaw U z μ =
      Measure.dirac (BouRabeeGwynne.CurveSpace.project (ContinuousMap.const _ z)) := by
  rw [stoppedBrownianLaw]
  have h : stoppedBrownianCurve U z =ᵐ[μ]
      (fun _ => BouRabeeGwynne.CurveSpace.project (ContinuousMap.const _ z)) := by
    filter_upwards [hzero] with ω hω
    have ht : continuousExitTime U z ω = 0 :=
      continuousExitTime_eq_zero_of_not_mem (by simpa only [hω, add_zero] using hz)
    apply congrArg BouRabeeGwynne.CurveSpace.project
    apply ContinuousMap.ext
    intro t
    change z + ω ⟨(t : ℝ) * (continuousExitTime U z ω).toNNReal, _⟩ = z
    simp only [ht, ENNReal.toNNReal_zero, NNReal.coe_zero, mul_zero]
    change z + ω 0 = z
    rw [hω, add_zero]
  rw [Measure.map_congr h, Measure.map_const, measure_univ, one_smul]

end LatticeProb
end
