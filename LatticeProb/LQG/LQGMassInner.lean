import Mathlib
import LatticeProb.LQG.LQGMeasureLocality2

/-!
# Inner measurability of the LQG mass

.

* `LatticeProb.LQG.fieldSigmaAlgebra_mono_of_subset`: `σ(h|_U) ≤ σ(h|_O)` for `U ⊆ O`.
* `LatticeProb.LQG.lqgMassInnerMeasurable_of_gff`: measurability of the inner LQG mass, which follows from the locality
  of the LQG measure (Fact 2.1 II of [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795]).
  The locality input is the unconditional locality `lqgLocality_of_gff` (`LatticeProb/LQG/LQGMeasureLocality2.lean`).
-/

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal NNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

/-- `σ(h|_U) ≤ σ(h|_O)` for `U ⊆ O`: a test function supported in `U` is supported in `O`. -/
theorem fieldSigmaAlgebra_mono_of_subset {Ω : Type*} (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) {U O : Set ℂ}
    (hUO : U ⊆ O) : fieldSigmaAlgebra α₀ hC U ≤ fieldSigmaAlgebra α₀ hC O := by
  unfold fieldSigmaAlgebra
  refine iSup₂_le fun φ hφ => ?_
  obtain ⟨h1, h2, h3⟩ := hφ
  exact le_iSup₂_of_le φ (show IsTestFunction O φ from ⟨h1, h2, h3.trans hUO⟩) le_rfl

/-- **Inner measurability of the LQG mass.** For an open `O`
containing the closure of a bounded open `U`, the mass `μ ω U` is a.s. equal to a `σ(h|_O)`-measurable variable: it is
`σ(h|_U)`-measurable by the unconditional locality `lqgLocality_of_gff`, and `σ(h|_U) ≤ σ(h|_O)`. -/
theorem lqgMassInnerMeasurable_of_gff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (O U : Set ℂ) (_hO : IsOpen O) (hU : IsOpen U)
    (_hbdd : Bornology.IsBounded U) (hcl : closure U ⊆ O) :
    ∃ g : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC O] g ∧ ∀ᵐ ω ∂P, μ ω U = g ω := by
  obtain ⟨Y, hYm, hYae⟩ := lqgLocality_of_gff P γ α₀ hC hcirc hGFF hγ hγ2 hα μ hμ U hU
  exact ⟨Y, hYm.mono (fieldSigmaAlgebra_mono_of_subset α₀ hC (subset_closure.trans hcl)) le_rfl, hYae⟩

end LatticeProb.LQG
