import LatticeProb.Euclidean.ParentBlockSeparation
import LatticeProb.Prob.BrownianChainInBall

/-!
# Parent-block exit chains of planar Brownian motion

A chain of exits from parent blocks of squares has separated successive positions. If the chain
stays in a larger parent block, the separated-chain estimate bounds its probability uniformly in
the positions of the squares and the starting point.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

universe u

namespace LatticeProb.ParentBlock

/-- A chain of exits from side-`s` parent blocks, confined to a larger parent block, inherits the
superpolynomial Brownian separated-chain bound. The final time is included in the confinement
hypothesis. -/
theorem measure_parentBlock_chain_superpoly {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)), IsBrownianSpace 2 0 B P →
      ∀ (z c : ℂ) (S s : ℝ), 0 ≤ S → 0 ≤ s → z ∈ closedSquare c S →
      ∀ a : ℝ≥0, 0 < a → ∀ r : ℝ≥0, 0 < r → r < 1 →
      4 * S < (a : ℝ) → 2 * ((a : ℝ) * r) ≤ s →
      P {ω | ∃ (τ : ℕ → ℝ≥0) (centres : ℕ → ℂ), Monotone τ ∧
          (∀ n < ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊,
            z + Complex.orthonormalBasisOneI.repr.symm (B (τ n) ω) ∈ closedSquare (centres n) s ∧
            z + Complex.orthonormalBasisOneI.repr.symm (B (τ (n + 1)) ω) ∉
              interior (parentBlock (centres n) s)) ∧
          ∀ t ≤ τ ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊,
            z + Complex.orthonormalBasisOneI.repr.symm (B t ω) ∈ parentBlock c S}
        ≤ ENNReal.ofReal (C * (r : ℝ) ^ p) := by
  obtain ⟨C, hC⟩ := measure_separated_chain_in_ball_superpoly_scaled.{u} 2 two_pos hζ0 hζ1 p
  refine ⟨C, fun Ω _ P _ B hB z c S s hS hs hz a ha r hr hr1 hbig hsmall => ?_⟩
  refine le_trans (measure_mono ?_) (hC Ω P B hB a ha r hr hr1)
  rintro ω ⟨τ, centres, hτ, hexit, hin⟩
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro n hn
    obtain ⟨hstart, hend⟩ := hexit n hn
    have h := side_le_norm_sub_of_not_mem_interior_parentBlock hs hstart hend
    have heq :
        ‖(z + Complex.orthonormalBasisOneI.repr.symm (B (τ (n + 1)) ω)) -
          (z + Complex.orthonormalBasisOneI.repr.symm (B (τ n) ω))‖ =
          ‖B (τ (n + 1)) ω - B (τ n) ω‖ := by
      rw [add_sub_add_left_eq_sub, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hsmall.trans (heq ▸ h)
  · intro t ht
    have h := norm_sub_le_four_mul_of_mem_of_mem_parentBlock hS hz (hin t ht)
    have heq : ‖(z + Complex.orthonormalBasisOneI.repr.symm (B t ω)) - z‖ = ‖B t ω‖ := by
      rw [add_sub_cancel_left, LinearIsometryEquiv.norm_map]
    exact lt_of_le_of_lt (heq ▸ h) hbig

end LatticeProb.ParentBlock
