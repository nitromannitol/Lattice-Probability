import LatticeProb.Prob.NormalizedPrefixCurveEndpointLaw
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionKernel

/-! # Brownian stopped endpoints and path-clock laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- The endpoint law of the translated Brownian path and its exit clock agrees
with the endpoint of the stopped curve law. The two constructions of the curve
spaces need not be identified for this equality. -/
theorem map_brownian_pathClock_endpoint {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) (μ : Measure (BrownianPath d)) :
    (μ.map (fun ω => (translatedBrownianPath z ω, continuousExitTime U z ω))).map
      (fun p => p.1 p.2.toNNReal) =
        (stoppedBrownianLaw U z μ).map BouRabeeGwynne.CurveSpace.endPoint := by
  have hpath : Measurable (fun ω : BrownianPath d =>
      (translatedBrownianPath z ω, continuousExitTime U z ω)) :=
    (continuous_translatedBrownianPath.measurable.comp
      (measurable_const.prodMk measurable_id)).prodMk (measurable_continuousExitTime hU z)
  have heval : Measurable (fun p : BrownianPath d × ℝ≥0∞ => p.1 p.2.toNNReal) := by
    simpa only [normalizedPrefixCurve_endPoint, Function.comp_def] using
      CurveSpace.continuous_endPoint.measurable.comp measurable_normalizedPrefixCurve_toNNReal
  rw [Measure.map_map heval hpath, stoppedBrownianLaw,
    Measure.map_map BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable
      (measurable_stoppedBrownianCurve hU z)]
  congr 1
  funext ω
  change z + ω (continuousExitTime U z ω).toNNReal = _
  exact (stoppedBrownianCurve_endPoint (U := U) (z := z) (ω := ω)).symm

/-- The normalized prefix law on the path-clock carrier and the stopped curve
law have the same endpoint law in Euclidean space. -/
theorem map_brownian_prefix_endpoint {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) (μ : Measure (BrownianPath d)) :
    ((μ.map (fun ω => (translatedBrownianPath z ω, continuousExitTime U z ω))).map
      (fun p => normalizedPrefixCurve p.1 p.2.toNNReal)).map CurveSpace.endPoint =
        (stoppedBrownianLaw U z μ).map BouRabeeGwynne.CurveSpace.endPoint := by
  rw [map_endPoint_normalizedPrefixCurve, map_brownian_pathClock_endpoint hU z μ]

end LatticeProb
end
