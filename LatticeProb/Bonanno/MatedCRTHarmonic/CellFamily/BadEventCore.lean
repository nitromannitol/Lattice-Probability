/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.BadEventCore at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Core

/-!
# Outer-measure union bounds for the scaled-grid estimate

These lemmas use `Measure` on arbitrary sets, hence its underlying outer measure. They require no
measurability of the good or bad events.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellFamily

/-- Outer-measure union bound for the complement of a finite intersection. -/
theorem measure_finset_iInter_compl_le_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω) :
    μ (⋂ i ∈ s, E i)ᶜ ≤ ∑ i ∈ s, μ (E i)ᶜ := by
  have heq : (⋂ i ∈ s, E i)ᶜ = ⋃ i ∈ s, (E i)ᶜ := by
    ext ω
    simp
  rw [heq]
  exact measure_biUnion_finset_le s (fun i => (E i)ᶜ)

/-- Finite-intersection outer-measure bound when each bad event has a common upper bound. -/
theorem measure_finset_iInter_compl_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω) {δ : ℝ≥0∞}
    (hbad : ∀ i ∈ s, μ (E i)ᶜ ≤ δ) :
    μ (⋂ i ∈ s, E i)ᶜ ≤ (s.card : ℝ≥0∞) * δ := by
  calc
    μ (⋂ i ∈ s, E i)ᶜ ≤ ∑ i ∈ s, μ (E i)ᶜ :=
      measure_finset_iInter_compl_le_sum μ s E
    _ ≤ ∑ i ∈ s, δ := by
      exact Finset.sum_le_sum hbad
    _ = (s.card : ℝ≥0∞) * δ := by simp [Finset.sum_const, nsmul_eq_mul]

end MatedCRTHarmonic.CellFamily
