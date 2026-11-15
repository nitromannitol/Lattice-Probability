import LatticeProb.Walk.CellConfigStoppedExitComparison
import LatticeProb.Topology.StoppedRayIntervalDistance

/-! # Finite curves at continuous and vertex exits -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The finite curves obtained by stopping at the continuous exit and at the
first exterior vertex are close in the curve metric, with an error controlled
by the diameters of the two cells on the final edge. -/
theorem edist_stopped_interpolatedWalk_exit_curves_le (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) {U : Set Plane} (hU : IsOpen U)
    (hconv : Convex ℝ U) (hstart : (ε : ℝ) • p (ω 0) ∈ U)
    (hfin : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω ≠ ⊤) :
    ∃ n : ℕ,
      hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ) ∧
      let τ := continuousExitTime U 0 (H.interpolatedWalk p ε ω)
      τ ≠ ∞ ∧
      edist (normalizedPrefixCurve (H.interpolatedWalk p ε ω) τ.toNNReal)
        (normalizedPrefixCurve (H.interpolatedWalk p ε ω)
          ⟨(ε : ℝ) ^ 2 * H.jumpTime ω (n + 1),
            mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos (n + 1))⟩) ≤
        ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
          Metric.diam ((ω (n + 1)).1 : Set Plane)))) := by
  obtain ⟨n, hn, hf, hdist⟩ :=
    stopped_interpolatedWalk_exit_comparison H hH p hp ω hpos hunb hadj hε hU hconv hstart hfin
  refine ⟨n, hn, hf, ?_⟩
  rw [← StoppedRayIntervalDistance.reparamEDist_stopped_eq_normalizedPrefixCurve
    (H.interpolatedWalk p ε ω) (H.interpolatedWalk p ε ω)
    (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal
    ⟨(ε : ℝ) ^ 2 * H.jumpTime ω (n + 1),
      mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos (n + 1))⟩]
  refine (ReparamEDist.reparamEDist_le_iSup_edist _ _).trans (iSup_le fun t => ?_)
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hdist t)

end LatticeProb.CellConfigInterpolation
end
