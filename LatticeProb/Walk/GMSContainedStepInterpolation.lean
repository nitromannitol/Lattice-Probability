import LatticeProb.Walk.GMSScaledAdjacentJump
import LatticeProb.Walk.CellConfigStepInterpolation

/-! # Comparison of scaled walks on contained windows -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.GMSScaledAdjacentJump

/-- On a contained time window, scaled interpolation and step paths are
uniformly close for all sufficiently small positive scales. -/
theorem ae_scaled_interpolatedPath_dist_walk_lt
    {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hL : ConnectedAlongLines μ) (hMT : MassTransport μ) (hFE : FiniteExpectation μ) :
    ∀ᵐ H ∂μ, ∀ R : ℝ, ∀ δ > 0, ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (p : H.1.cells → Plane), (∀ K, p K ∈ (K.1 : Set Plane)) →
      ∀ (ω : ℕ → H.1.cells), (∀ K, 0 < H.1.holding K) →
      H.1.JumpTimesUnbounded ω → (∀ n, H.1.Adj (ω n) (ω (n + 1))) →
      ∀ S : ℝ, (∀ s, 0 ≤ s → s ≤ S →
        ε • H.1.interpolatedPath p ω s ∈ closedBall (0 : Plane) R) →
      ∀ s, 0 ≤ s → s ≤ S →
        dist (ε • H.1.interpolatedPath p ω s) (ε • p (H.1.walk ω s)) < δ := by
  filter_upwards [ae_scaled_adjacent_jump_lt hL hMT hFE] with H hjump
  intro R δ hδ
  obtain ⟨ε₀, hε₀, hsmall⟩ := hjump R δ hδ
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hε₀ p hp ω hpos hunb hadj S hcontained s hs hsS
  obtain ⟨n, hn, hn'⟩ := H.1.exists_mem_Ico hpos hunb hs
  have hknot : H.1.interpolatedPath p ω (H.1.jumpTime ω n) = p (ω n) := by
    rw [H.1.interpolatedPath_eq_of_mem hpos le_rfl
      (H.1.jumpTime_strictMono hpos (Nat.lt_succ_self n)), H.1.affinePiece_self]
  have hball : ε • p (ω n) ∈ closedBall (0 : Plane) R := by
    rw [← hknot]
    exact hcontained _ (H.1.jumpTime_nonneg hpos n) (hn.trans hsS)
  have hsmalljump := hsmall ε hε hε₀ p hp (ω n) (ω (n + 1)) hball (hadj n)
  have hdist := CellConfigStepInterpolation.dist_interpolatedPath_walk_le H.1 p ω hpos hn hn'
  rw [dist_smul₀, Real.norm_of_nonneg hε.le]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hdist hε.le) hsmalljump

end LatticeProb.GMSScaledAdjacentJump
end
