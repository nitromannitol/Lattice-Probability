import LatticeProb.Walk.FinitePrefixCurveLawComparison
import LatticeProb.Walk.CountableSourceCurveLaw

/-! # Finite-prefix curve law comparison on countable cells -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The finite-prefix law comparison has measurable observables on countable
cell spaces with measurable singletons. -/
theorem levyProkhorov_continuousExitCurve_le_of_prefix_countable (H : CellConfig)
    [Countable H.cells] [MeasurableSpace H.cells] [MeasurableSingletonClass H.cells]
    (hH : H.IsCellConfiguration)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (hpos : ∀ K, 0 < H.holding K) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    {U : Set Plane} (hU : IsOpen U) (hconv : Convex ℝ U)
    (P : Measure (ℕ → H.cells)) (E : Set (ℕ → H.cells)) (r s : ℝ≥0)
    (hbad : P E ≤ (r : ℝ≥0∞))
    (hgood : ∀ᵐ ω ∂P, ω ∉ E →
      (ε : ℝ) • p (ω 0) ∈ U ∧
      ∃ n, hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ) ∧
      (∀ j ≤ n, H.Adj (ω j) (ω (j + 1))) ∧
      ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
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
  exact levyProkhorov_continuousExitCurve_le_of_prefix H hH p hp hpos hε hm hU hconv
    P E r s hbad hgood (measurable_sourceContinuousExitCurve H p ε m hU).aemeasurable
    (measurable_stoppedPolygonalCurve_countable _ _).aemeasurable ν hsource

end LatticeProb.CellConfigInterpolation
end
