import LatticeProb.Walk.CellConfigExitRestart
import LatticeProb.Prob.CellConfigWalkMeasurable

/-!
# Finite exit of an interpolated cell walk

Visiting a cell whose representative lies outside a domain forces finite exit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- At a rescaled jump time the interpolated walk is at the rescaled representative. -/
theorem interpolatedWalk_at_jumpTime (H : CellConfig) (p : H.cells → Plane)
    (ω : ℕ → H.cells) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) (k : ℕ) {ε : ℝ≥0} (hε : 0 < ε) :
    H.interpolatedWalk p ε ω
      ⟨(ε : ℝ) ^ 2 * H.jumpTime ω k,
        mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos k)⟩ = (ε : ℝ) • p (ω k) := by
  let t : ℝ≥0 := ⟨(ε : ℝ) ^ 2 * H.jumpTime ω k,
    mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos k)⟩
  have he : (ε : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  rw [show H.interpolatedWalk p ε ω t =
    (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2) from
      congrFun (H.coe_interpolatedWalk hpos hunb ε) t]
  have ht : (t : ℝ) / (ε : ℝ) ^ 2 = H.jumpTime ω k := by
    dsimp [t]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ he)
  rw [ht, H.interpolatedPath_eq_of_mem hpos le_rfl
    (H.jumpTime_strictMono hpos (Nat.lt_succ_self k)), H.affinePiece_self]

/-- If a rescaled representative is outside the domain, the exit time is finite. -/
theorem continuousExitTime_ne_top_of_visit (H : CellConfig) (p : H.cells → Plane)
    (ω : ℕ → H.cells) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) {ε : ℝ≥0} (hε : 0 < ε) (U : Set Plane)
    (k : ℕ) (hout : (ε : ℝ) • p (ω k) ∉ U) :
    continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞ := by
  let t : ℝ≥0 := ⟨(ε : ℝ) ^ 2 * H.jumpTime ω k,
    mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos k)⟩
  have ht : (0 : Plane) + H.interpolatedWalk p ε ω t ∉ U := by
    rw [zero_add]
    change H.interpolatedWalk p ε ω ⟨(ε : ℝ) ^ 2 * H.jumpTime ω k, _⟩ ∉ U
    rw [interpolatedWalk_at_jumpTime H p ω hpos hunb k hε]
    exact hout
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (continuousExitTime_le_of_not_mem ht)

/-- Almost-sure visits to exterior representatives give almost-sure finite exit. -/
theorem ae_continuousExitTime_ne_top_of_visit (H : CellConfig) (p : H.cells → Plane)
    (hpos : ∀ K, 0 < H.holding K) {ε : ℝ≥0} (hε : 0 < ε) (U : Set Plane)
    (Q : Measure (ℕ → H.cells))
    (hunb : ∀ᵐ ω ∂Q, H.JumpTimesUnbounded ω)
    (hvisit : ∀ᵐ ω ∂Q, ∃ k, (ε : ℝ) • p (ω k) ∉ U) :
    ∀ᵐ ω ∂Q, continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞ := by
  filter_upwards [hunb, hvisit] with ω hω ⟨k, hk⟩
  exact continuousExitTime_ne_top_of_visit H p ω hpos hω hε U k hk

/-- A recurrent cell walk exits in finite time if it almost surely visits an
exterior representative. -/
theorem ae_continuousExitTime_ne_top_of_recurrent_visit (H : CellConfig)
    (p : H.cells → Plane) (hpos : ∀ K, 0 < H.holding K) (hrec : H.Recurrent)
    {ε : ℝ≥0} (hε : 0 < ε) (U : Set Plane) {x : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw x Q)
    (hvisit : ∀ᵐ ω ∂Q, ∃ k, (ε : ℝ) • p (ω k) ∉ U) :
    ∀ᵐ ω ∂Q, continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞ :=
  ae_continuousExitTime_ne_top_of_visit H p hpos hε U Q
    (CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hQ) hvisit

end LatticeProb.CellConfigInterpolation
end
