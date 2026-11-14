import LatticeProb.Walk.CellConfigExteriorHitBracket

/-! # Clock discrepancy at the exterior hit of a cell walk -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The first exterior jump clock exceeds the continuous exit clock by less
than the scaled holding time of the preceding cell. -/
theorem continuousExitTime_clock_gap_of_hitTime (H : CellConfig)
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
      (ε : ℝ) ^ 2 * H.jumpTime ω n < (τ.toNNReal : ℝ) ∧
      (τ.toNNReal : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) ∧
      0 ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) - (τ.toNNReal : ℝ) ∧
      (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) - (τ.toNNReal : ℝ) <
        (ε : ℝ) ^ 2 * H.holding (ω n) ∧
      dist ((H.interpolatedWalk p ε ω) τ.toNNReal)
        ((ε : ℝ) • p (stopState (hitTime {K : H.cells | (ε : ℝ) • p K ∉ U}) ω)) ≤
        (ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
          Metric.diam ((ω (n + 1)).1 : Set Plane)) := by
  obtain ⟨n, hn, hf, hlo, hhi, hd⟩ :=
    continuousExitTime_bracket_of_hitTime H hH p hp ω hpos hunb hadj hε hU hconv hstart hfin
  refine ⟨n, hn, hf, hlo, hhi, sub_nonneg.mpr hhi, ?_, hd⟩
  rw [H.jumpTime_succ, mul_add]
  linarith

end LatticeProb.CellConfigInterpolation
end
