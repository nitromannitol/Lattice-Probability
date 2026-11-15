import LatticeProb.Prob.WilliamsGluePathwise
import LatticeProb.Prob.WilliamsPostLastPath

/-! # Almost-sure equality of Williams gluing constructions -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

open QuantumZipper QuantumZipper.Williams

/-- On the full-measure event where the continuation starts at zero, the two
pathwise gluing constructions coincide. -/
theorem ae_williams_glue_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b b' : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (hb' : GoodBM b' P)
    {σ μ c : ℝ} (hσ : 0 < σ) (hμ : 0 < μ)
    (hhit : ∀ ω, ∃ t, dpath σ (-μ) b ω t = -c) :
    ∀ᵐ ω ∂P, (glueC c ⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩
      (williamsPostLastPath hb' σ μ ω) : ℝ≥0 → ℝ) =
        glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) := by
  filter_upwards [ae_williamsPostLastPath_zero hb' hσ hμ] with ω hz
  obtain ⟨t, ht⟩ := hhit ω
  let X : C(ℝ≥0, ℝ) := ⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩
  have hfin : hitFrom (-c) 0 (X : ℝ≥0 → ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hitFrom_le zero_le ht)
  exact (glued_eq_glueC (dpath_zero hb σ (-μ) ω) hz hfin (fun _ => rfl)).symm

end LatticeProb
