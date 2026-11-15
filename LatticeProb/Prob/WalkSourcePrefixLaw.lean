import LatticeProb.Prob.WalkExitPathClockLaw
import LatticeProb.Walk.CellConfigContinuousExitClock
import LatticeProb.Topology.CurveSpaceComparison

/-! # Exit-prefix laws under changes of walk clock -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

/-- The holding-time and constant-step interpolations have the same law for
finite continuous-exit curves, expressed in the source curve space. -/
theorem map_walkExitPathClockLaw_sourcePrefix_eq_constantStep
    {H : CellConfig} [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    {U : Set Plane} (hU : IsOpen U)
    (hfinite : ∀ᵐ ω ∂Q, continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞) :
    (walkExitPathClockLaw H p ε U Q).map
      (fun q => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve q.1 q.2.toNNReal)) =
    Q.map (fun ω =>
      let g := ConstantStepInterpolation.continuousPlanePath m
        (fun n => (ε : ℝ) • p (ω n))
      CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal)) := by
  have hcurve : Measurable (fun q : C(ℝ≥0, Plane) × ℝ≥0∞ =>
      CurveSpaceComparison.isometryEquiv 2 (normalizedPrefixCurve q.1 q.2.toNNReal)) :=
    (CurveSpaceComparison.isometryEquiv 2).continuous.measurable.comp
      measurable_normalizedPrefixCurve_toNNReal
  rw [walkExitPathClockLaw, AEMeasurable.map_map_of_aemeasurable hcurve.aemeasurable
    (aemeasurable_interpolatedWalk_exitPathClock hrec hpos hQ p ε hU)]
  apply Measure.map_congr
  filter_upwards [ae_jumpTimesUnbounded_of_recurrent hrec hpos hQ, hfinite] with ω hunb hfin
  obtain ⟨φ, _, hφ⟩ :=
    CellConfigInterpolation.exists_orderIso_interpolatedWalk_eq_constantStep
      H p ω hpos hunb hε hm
  obtain ⟨_, heq⟩ := normalized_exit_curve_eq_of_orderIso
    (H.interpolatedWalk p ε ω)
    (ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n)))
    φ hφ hU hfin
  exact congrArg (CurveSpaceComparison.isometryEquiv 2) heq

end LatticeProb.CellConfigWalk
end
