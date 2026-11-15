import LatticeProb.Walk.CellConfigContinuousExitClock
import LatticeProb.Walk.PolygonalPrefixSpeed
import LatticeProb.Topology.CurveSpaceComparison

/-! # Final-edge estimate in the polygonal curve space -/

set_option autoImplicit false
noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The continuous exit curve and the polygonal curve through the first
exterior vertex differ by at most the diameter error of the final edge. -/
theorem source_edist_exit_curve_le (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m) {U : Set Plane}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hstart : (ε : ℝ) • p (ω 0) ∈ U)
    (hfin : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω ≠ ⊤) :
    ∃ n : ℕ,
      hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ) ∧
      let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
      continuousExitTime U 0 g ≠ ∞ ∧
      edist (CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal))
        (BouRabeeGwynne.CurveSpace.project
          (polygonalCurve (fun n => (ε : ℝ) • p (ω n)) id (n + 1))) ≤
        ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
          Metric.diam ((ω (n + 1)).1 : Set Plane)))) := by
  obtain ⟨n, hn, hf, hd⟩ := edist_constantStep_exit_curve_le H hH p hp ω hpos hunb hadj
    hε hm hU hconv hstart hfin
  refine ⟨n, hn, hf, ?_⟩
  rw [← CurveSpaceComparison.isometryEquiv_project,
    ← normalizedPathPrefix_constantStep_knot_eq_polygonalCurve _ hm,
    ← normalizedPrefixCurve]
  exact (CurveSpaceComparison.isometryEquiv 2).isometry.edist_eq _ _ ▸ hd

end LatticeProb.CellConfigInterpolation
end
