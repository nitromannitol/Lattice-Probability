import LatticeProb.Prob.BrownianStoppedPathClock
import LatticeProb.Topology.CurveSpaceComparison

/-! # Stopped Brownian curves and path-clock prefix laws -/

set_option autoImplicit false
noncomputable section

open MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- The source-space prefix of the translated path at its exit clock has the
same law as the stopped Brownian curve. -/
theorem map_brownian_pathClock_sourcePrefix {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) (μ : Measure (BrownianPath d)) :
    (μ.map (fun ω => (translatedBrownianPath z ω, continuousExitTime U z ω))).map
      (fun p => CurveSpaceComparison.isometryEquiv d
        (normalizedPrefixCurve p.1 p.2.toNNReal)) = stoppedBrownianLaw U z μ := by
  have hpath : Measurable (fun ω : BrownianPath d =>
      (translatedBrownianPath z ω, continuousExitTime U z ω)) :=
    (continuous_translatedBrownianPath.measurable.comp
      (measurable_const.prodMk measurable_id)).prodMk (measurable_continuousExitTime hU z)
  have hcurve : Measurable (fun p : BrownianPath d × ℝ≥0∞ =>
      CurveSpaceComparison.isometryEquiv d (normalizedPrefixCurve p.1 p.2.toNNReal)) :=
    (CurveSpaceComparison.isometryEquiv d).continuous.measurable.comp
      measurable_normalizedPrefixCurve_toNNReal
  rw [Measure.map_map hcurve hpath, stoppedBrownianLaw]
  congr 1

end LatticeProb
end
