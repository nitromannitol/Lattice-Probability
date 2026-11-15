import LatticeProb.Walk.SourceStoppedCurveFinalEdge
import LatticeProb.Bonanno.BouRabeeGwynne.ReconstructedLawComparison

/-! # Laws of continuous and polygonal exit curves -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- An exceptional-set bound and the final-edge estimate compare the two
stopped-curve laws on the same walk, and hence with any third curve law. -/
theorem levyProkhorov_continuousExitCurve_le (H : CellConfig)
    [MeasurableSpace H.cells] (hH : H.IsCellConfiguration)
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
    (hX : AEMeasurable (fun ω : ℕ → H.cells =>
      let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
      CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal)) P)
    (hY : AEMeasurable (stoppedPolygonalCurve (fun K => (ε : ℝ) • p K)
      {K : H.cells | (ε : ℝ) • p K ∈ U}) P)
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
  let X := fun ω : ℕ → H.cells =>
    let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
    CurveSpaceComparison.isometryEquiv 2
      (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal)
  let Y := stoppedPolygonalCurve (fun K : H.cells => (ε : ℝ) • p K)
    {K : H.cells | (ε : ℝ) • p K ∈ U}
  have hXY : levyProkhorovEDist (P.map X) (P.map Y) ≤ (r : ℝ≥0∞) := by
    apply levyProkhorov_curveLaws_le_of_ae_good P X Y hX hY E r hbad
    filter_upwards [hgood] with ω hω
    intro hωE
    obtain ⟨hunb, hadj, hstart, hfin, hdiam⟩ := hω hωE
    obtain ⟨n, _, _, hdist⟩ := source_edist_exit_stoppedPolygonalCurve_le
      H hH p hp ω hpos hunb hadj hε hm hU hconv hstart hfin
    exact hdist.trans_lt (hdiam n)
  exact (levyProkhorovEDist_triangle (P.map X) (P.map Y) ν).trans
    (add_le_add hXY hsource)

end LatticeProb.CellConfigInterpolation
end
