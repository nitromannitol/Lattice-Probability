import LatticeProb.Walk.CellConfigExteriorExitBracket
import LatticeProb.Walk.CellConfigHittingRestart

/-!
# First exterior hit and continuous exit

The discrete first hit of the exterior identifies the edge containing the exit
of a linearly interpolated cell walk from an open convex domain.
-/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- Starting outside makes both the discrete hit and the continuous exit zero. -/
theorem exterior_hitTime_and_exit_eq_zero (H : CellConfig) (p : H.cells → Plane)
    (ω : ℕ → H.cells) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) {ε : ℝ≥0} (hε : 0 < ε)
    (U : Set Plane) (hout : (ε : ℝ) • p (ω 0) ∉ U) :
    hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = 0 ∧
      continuousExitTime U 0 (H.interpolatedWalk p ε ω) = 0 := by
  refine ⟨hitTime_eq_zero_iff.mpr hout, ?_⟩
  apply le_antisymm ?_ bot_le
  have ht : (0 : Plane) + H.interpolatedWalk p ε ω 0 ∉ U := by
    rw [zero_add]
    have hz : (⟨(ε : ℝ) ^ 2 * H.jumpTime ω 0,
        mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos 0)⟩ : ℝ≥0) = 0 := by
      apply Subtype.ext
      simp [CellConfig.jumpTime]
    have hw := interpolatedWalk_at_jumpTime H p ω hpos hunb 0 hε
    rw [hz] at hw
    exact hw.symm ▸ hout
  simpa using continuousExitTime_le_of_not_mem ht

/-- The finite first exterior hit of a walk started inside occurs at a successor
index, whose preceding edge brackets the continuous exit and controls its error. -/
theorem continuousExitTime_bracket_of_hitTime (H : CellConfig)
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
      dist ((H.interpolatedWalk p ε ω) τ.toNNReal)
        ((ε : ℝ) • p (stopState (hitTime {K : H.cells | (ε : ℝ) • p K ∉ U}) ω)) ≤
        (ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
          Metric.diam ((ω (n + 1)).1 : Set Plane)) := by
  let A : Set H.cells := {K | (ε : ℝ) • p K ∉ U}
  have ht : hitTime A ω = ((hitTime A ω).toNat : ℕ) := (coe_toNat_hitTime hfin).symm
  have hh := hitTime_eq_coe_iff.mp ht
  have hn : (hitTime A ω).toNat ≠ 0 := by
    intro h
    rw [h] at hh
    exact hh.1 hstart
  obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have ht' : hitTime A ω = (n + 1 : ℕ) := by simpa only [hn'] using ht
  have hh' := hitTime_eq_coe_iff.mp ht'
  have hi : ∀ j ≤ n, (ε : ℝ) • p (ω j) ∈ U := by
    intro j hj
    by_contra h
    exact hh'.2 j (Nat.lt_succ_of_le hj) h
  have hs : stopState (hitTime A) ω = ω (n + 1) := stopState_eq_of_eq ht'
  refine ⟨n, ht', ?_⟩
  rw [hs]
  exact continuousExitTime_bracket_of_first_exterior H hH p hp ω hpos hunb n
    (hadj n) hε hU hconv hi hh'.1

end LatticeProb.CellConfigInterpolation
end
