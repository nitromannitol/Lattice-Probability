import LatticeProb.Walk.CellConfigExteriorHitBracket
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties

/-! # The exterior hit of an interpolated cell walk -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The first exterior representative is close to the frontier, with error
controlled by the diameters of the two cells on the exit edge. -/
theorem exists_frontier_near_exterior_hit (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) {U : Set Plane} (hU : IsOpen U)
    (hconv : Convex ℝ U) (hstart : (ε : ℝ) • p (ω 0) ∈ U)
    (hfin : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω ≠ ⊤) :
    ∃ n : ℕ, hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ) ∧
      let τ := continuousExitTime U 0 (H.interpolatedWalk p ε ω)
      τ ≠ ∞ ∧
      (ε : ℝ) ^ 2 * H.jumpTime ω n < (τ.toNNReal : ℝ) ∧
      (τ.toNNReal : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) ∧
      ∃ z ∈ frontier U,
        dist ((ε : ℝ) • p (stopState (hitTime {K : H.cells | (ε : ℝ) • p K ∉ U}) ω)) z ≤
          (ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
            Metric.diam ((ω (n + 1)).1 : Set Plane)) := by
  obtain ⟨n, hn, hf, hlo, hhi, hd⟩ :=
    continuousExitTime_bracket_of_hitTime H hH p hp ω hpos hunb hadj hε hU hconv hstart hfin
  refine ⟨n, hn, hf, hlo, hhi,
    (H.interpolatedWalk p ε ω) (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal,
    ?_, ?_⟩
  · have hz : (⟨(ε : ℝ) ^ 2 * H.jumpTime ω 0,
        mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos 0)⟩ : ℝ≥0) = 0 := by
      apply Subtype.ext
      simp [CellConfig.jumpTime]
    have hw := interpolatedWalk_at_jumpTime H p ω hpos hunb 0 hε
    rw [hz] at hw
    have hstart0 : (0 : Plane) + H.interpolatedWalk p ε ω 0 ∈ U := by
      simpa only [zero_add] using hw.symm ▸ hstart
    simpa only [zero_add] using continuousExitTime_mem_frontier hU hstart0 hf
  · simpa only [dist_comm] using hd

end LatticeProb.CellConfigInterpolation
end
