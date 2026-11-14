import LatticeProb.Prob.BrownianParentBlockChain
import LatticeProb.Prob.ContinuousPathExitConfinement

/-!
# Parent-block chains before an outer exit

The separated-chain estimate applies to chains that end before the first exit from the interior
of a larger parent block. The path may start on the boundary and the exit may be infinite.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

universe u

namespace LatticeProb.ParentBlock

/-- A chain of parent-block exits completed by the first exit from the interior of a larger
parent block satisfies the superpolynomial separated-chain estimate. -/
theorem measure_parentBlock_chain_before_exit_superpoly {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)), IsBrownianSpace 2 0 B P →
      ∀ (z c : ℂ) (S s : ℝ), 0 ≤ S → 0 ≤ s → z ∈ closedSquare c S →
      ∀ a : ℝ≥0, 0 < a → ∀ r : ℝ≥0, 0 < r → r < 1 →
      4 * S < (a : ℝ) → 2 * ((a : ℝ) * r) ≤ s →
      P {ω | let f := fun t : ℝ≥0 => z + Complex.orthonormalBasisOneI.repr.symm (B t ω)
        Continuous f ∧ f 0 ∈ parentBlock c S ∧
        ∃ (τ : ℕ → ℝ≥0) (centres : ℕ → ℂ), Monotone τ ∧
          (∀ n < ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊,
            f (τ n) ∈ closedSquare (centres n) s ∧
            f (τ (n + 1)) ∉ interior (parentBlock (centres n) s)) ∧
          (τ ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊ : ℝ≥0∞) ≤
            openExitTime (fun t (_ : Unit) => f t) (interior (parentBlock c S)) ()}
        ≤ ENNReal.ofReal (C * (r : ℝ) ^ p) := by
  obtain ⟨C, hC⟩ := measure_parentBlock_chain_superpoly.{u} hζ0 hζ1 p
  refine ⟨C, fun Ω _ P _ B hB z c S s hS hs hz a ha r hr hr1 hbig hsmall => ?_⟩
  refine le_trans (measure_mono ?_) (hC Ω P B hB z c S s hS hs hz a ha r hr hr1 hbig hsmall)
  rintro ω ⟨hcont, hstart, τ, centres, hτ, hexit, htime⟩
  refine ⟨τ, centres, hτ, hexit, ?_⟩
  intro t ht
  have hclosed : IsClosed (parentBlock c S) := by
    rw [parentBlock_eq hS]
    exact isClosed_closedSquare c (3 * S)
  exact mem_closed_of_le_openExitTime isOpen_interior hclosed interior_subset hcont hstart
    ((ENNReal.coe_le_coe.mpr ht).trans htime)

end LatticeProb.ParentBlock
