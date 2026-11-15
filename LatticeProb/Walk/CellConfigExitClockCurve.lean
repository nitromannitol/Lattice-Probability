import LatticeProb.Walk.CellConfigStoppedExitCurve
import LatticeProb.Walk.CellConfigConstantStepComparison
import LatticeProb.Walk.CellConfigVisitPathLaw

/-! # Finite exit curves under changes of walk clock -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb

/-- A finite prefix defines the same curve after an increasing change of clock. -/
theorem normalizedPrefixCurve_eq_of_orderIso {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (φ : ℝ≥0 ≃o ℝ≥0)
    (h : ∀ t, f t = g (φ t)) (T : ℝ≥0) :
    normalizedPrefixCurve f T = normalizedPrefixCurve g (φ T) := by
  apply edist_eq_zero.mp
  refine le_antisymm ((normalizedPrefixCurve_edist_le_stopped_ray_cost_all f g T (φ T) φ).trans ?_) bot_le
  apply iSup_le
  intro t
  have hmin : min (φ t) (φ T) = φ (min t T) := (φ.monotone.map_min).symm
  rw [hmin, ← h, edist_self]

namespace CellConfigInterpolation

/-- The continuous exit curve of the holding-clock walk is close to the
first-exterior-vertex curve of its constant-step interpolation. -/
theorem edist_exit_curve_constantStep_le (H : CellConfig)
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
      let τ := continuousExitTime U 0 (H.interpolatedWalk p ε ω)
      τ ≠ ∞ ∧
      edist (normalizedPrefixCurve (H.interpolatedWalk p ε ω) τ.toNNReal)
        (normalizedPrefixCurve
          (ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n)))
          (ConstantStepInterpolation.knot m (n + 1))) ≤
        ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
          Metric.diam ((ω (n + 1)).1 : Set Plane)))) := by
  obtain ⟨n, hn, hf, hd⟩ :=
    edist_stopped_interpolatedWalk_exit_curves_le H hH p hp ω hpos hunb hadj hε hU hconv hstart hfin
  obtain ⟨φ, hφ, heq⟩ :=
    exists_orderIso_interpolatedWalk_eq_constantStep H p ω hpos hunb hε hm
  refine ⟨n, hn, hf, ?_⟩
  have hc := normalizedPrefixCurve_eq_of_orderIso (H.interpolatedWalk p ε ω)
    (ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n)))
    φ heq (scaledJumpTime H ω hpos ε (n + 1))
  rw [hφ] at hc
  rw [← hc]
  exact hd

end CellConfigInterpolation
end LatticeProb
end
