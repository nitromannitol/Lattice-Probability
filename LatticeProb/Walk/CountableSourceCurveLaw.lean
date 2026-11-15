import LatticeProb.Walk.SourceStoppedCurveLawComparison
import LatticeProb.Walk.CountableStoppedCurveMeasurable
import LatticeProb.Walk.CellConfigVisitPathLaw
import LatticeProb.Prob.BrownianPathSpace

/-! # Measurable stopped curves on countable cell sets -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov LatticeProb.CellConfigWalk
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The continuously stopped curve is measurable for countable cells, including
when the exit time is infinite and totalized to zero duration. -/
theorem measurable_sourceContinuousExitCurve (H : CellConfig)
    [Countable H.cells] [MeasurableSpace H.cells] [MeasurableSingletonClass H.cells]
    (p : H.cells → Plane) (a m : ℝ) {U : Set Plane} (hU : IsOpen U) :
    Measurable (fun ω : ℕ → H.cells =>
      let g := ConstantStepInterpolation.continuousPlanePath m (fun n => a • p (ω n))
      CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal)) := by
  have hp : Measurable (fun ω : ℕ → H.cells => fun n => a • p (ω n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable (fun K : H.cells => a • p K)).comp (measurable_pi_apply n)
  have hg := measurable_constantStepPath _ hp m
  have ht := (measurable_continuousExitTime hU 0).comp hg
  exact (CurveSpaceComparison.isometryEquiv 2).continuous.measurable.comp
    (measurable_normalizedPrefixCurve_toNNReal.comp (hg.prodMk ht))

/-- On countable cells the two stopped-curve measurability assumptions in the
final-edge comparison follow from the open-domain hypothesis. -/
theorem levyProkhorov_continuousExitCurve_le_countable (H : CellConfig)
    [Countable H.cells] [MeasurableSpace H.cells] [MeasurableSingletonClass H.cells]
    (hH : H.IsCellConfiguration)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (hpos : ∀ K, 0 < H.holding K) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    {U : Set Plane} (hU : IsOpen U) (hconv : Convex ℝ U)
    (P : Measure (ℕ → H.cells)) (E : Set (ℕ → H.cells)) (r s : ℝ≥0)
    (hbad : P E ≤ (r : ℝ≥0∞))
    (hgood : ∀ᵐ ω ∂P, ω ∉ E →
      H.JumpTimesUnbounded ω ∧ (∀ n, H.Adj (ω n) (ω (n + 1))) ∧
      (ε : ℝ) • p (ω 0) ∈ U ∧
      hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω ≠ ⊤ ∧
      ∀ n, ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
        Metric.diam ((ω (n + 1)).1 : Set Plane)))) < (r : ℝ≥0∞))
    (ν : Measure (BouRabeeGwynne.CurveSpace 2))
    (hsource : levyProkhorovEDist
      (P.map (stoppedPolygonalCurve (fun K => (ε : ℝ) • p K)
        {K : H.cells | (ε : ℝ) • p K ∈ U})) ν ≤ (s : ℝ≥0∞)) :
    levyProkhorovEDist
      (P.map (fun ω : ℕ → H.cells =>
        let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal))) ν ≤
      (r : ℝ≥0∞) + (s : ℝ≥0∞) := by
  exact levyProkhorov_continuousExitCurve_le H hH p hp hpos hε hm hU hconv
    P E r s hbad hgood (measurable_sourceContinuousExitCurve H p ε m hU).aemeasurable
    (measurable_stoppedPolygonalCurve_countable _ _).aemeasurable ν hsource

end LatticeProb.CellConfigInterpolation
end
