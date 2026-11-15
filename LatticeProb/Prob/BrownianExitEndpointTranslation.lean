import LatticeProb.Prob.BrownianStoppedPathClock
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties

/-! # Translation of stopped Brownian endpoint laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- Translating the domain and starting point translates the stopped endpoint
law, for any measure on continuous paths. -/
theorem stoppedBrownianLaw_endPoint_map_sub {d : ℕ}
    {V : Set (Euc d)} (hV : IsOpen V) (z a : Euc d)
    (μ : Measure (BrownianPath d)) :
    ((stoppedBrownianLaw V z μ).map BouRabeeGwynne.CurveSpace.endPoint).map
        (fun x => x - a) =
      (stoppedBrownianLaw ((fun x : Euc d => a + x) ⁻¹' V) (z - a) μ).map
        BouRabeeGwynne.CurveSpace.endPoint := by
  let W : Set (Euc d) := (fun x : Euc d => a + x) ⁻¹' V
  have hW : IsOpen W := hV.preimage (by fun_prop)
  have ht (ω : BrownianPath d) : continuousExitTime W (z - a) ω =
      continuousExitTime V z ω := by
    have hp : (fun t : ℝ≥0 => (z - a) + ω t ∉ W) =
        (fun t : ℝ≥0 => z + ω t ∉ V) := by
      funext t
      change (a + ((z - a) + ω t) ∉ V) = (z + ω t ∉ V)
      congr 1
      abel
    unfold continuousExitTime
    rw [hp]
  have hf : Measurable (fun x : Euc d => x - a) := by fun_prop
  rw [stoppedBrownianLaw, stoppedBrownianLaw,
    Measure.map_map BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable
      (measurable_stoppedBrownianCurve hV z),
    Measure.map_map hf (BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable.comp
      (measurable_stoppedBrownianCurve hV z)),
    Measure.map_map BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable
      (measurable_stoppedBrownianCurve hW (z - a))]
  congr 1
  funext ω
  simp only [Function.comp_apply, stoppedBrownianCurve_endPoint, ht]
  abel

end LatticeProb
end
