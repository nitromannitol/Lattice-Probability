/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/SpanningForest/FiniteUSTLimit.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.SpanningForest.FiniteUSTLimit in place of OAI.Probability.SpanningForest.FiniteUSTLimit, and the module paths of local imports are changed in the same way; the import of LatticeProb.OpenAI.Probability.SpanningForest.FUSFLawUnique (not copied here) is replaced by the imports of the copied modules it reaches,
   namely LatticeProb.OpenAI.Probability.SpanningForest.CylinderLimitMeasure, LatticeProb.OpenAI.Probability.SpanningForest.BinaryWeakConvergence, LatticeProb.OpenAI.Probability.SpanningForest.FiniteUSTMeasure, LatticeProb.OpenAI.Probability.SpanningForest.Definitions, LatticeProb.OpenAI.Probability.SpanningForest.BinaryLawUnique;
   the unused declarations `exists_finiteUST_limit`, `exists_hasFUSFLaw_of_common_cylinder_limits` (they need modules not copied here) are omitted; statements and proofs of the declarations kept are unchanged. -/
import LatticeProb.OpenAI.Probability.SpanningForest.CylinderLimitMeasure
import LatticeProb.OpenAI.Probability.SpanningForest.BinaryWeakConvergence
import LatticeProb.OpenAI.Probability.SpanningForest.FiniteUSTMeasure
import LatticeProb.OpenAI.Probability.SpanningForest.Definitions
import LatticeProb.OpenAI.Probability.SpanningForest.BinaryLawUnique

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336

def finiteUSTProbabilityMeasure (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) : ProbabilityMeasure EdgeConfiguration :=
  ⟨finiteUSTMeasure K, finiteUSTMeasure_isProbabilityMeasure K hK⟩



theorem finiteUSTMeasure_positiveCylinder (K : FiniteSubgraphCode)
    (A : Finset EdgeCode) :
    finiteUSTMeasure K {x | ∀ e ∈ A, x e = true} = ustCylinder K A ∅ := by
  simpa [edgeCylinder] using finiteUSTMeasure_edgeCylinder K A ∅

theorem exists_finiteUST_limit_of_inclusion_limits
    (H : ℕ → FiniteSubgraphCode)
    (hH : ∀ n, (spanningTrees (H n)).Nonempty)
    (L : Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ A, Tendsto (fun n => ustCylinder (H n) A ∅) atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      (∀ A, (μ : Measure EdgeConfiguration) {x | ∀ e ∈ A, x e = true} = L A) ∧
      Tendsto (fun n => finiteUSTProbabilityMeasure (H n) (hH n)) atTop (𝓝 μ) := by
  apply BinaryLaw.exists_weakLimit_of_positiveCylinder_limits
    (fun n => finiteUSTProbabilityMeasure (H n) (hH n)) L
  intro A
  simpa only [finiteUSTProbabilityMeasure, ProbabilityMeasure.coe_mk,
    finiteUSTMeasure_positiveCylinder] using hL A

theorem exists_hasFUSFLaw_of_common_inclusion_limits
    (G : GraphCode) (H : ℕ → FiniteSubgraphCode)
    (hH : IsConnectedExhaustion G H)
    (hne : ∀ H' : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H' →
      ∀ n, (spanningTrees (H' n)).Nonempty)
    (L : Finset EdgeCode → ℝ≥0∞)
    (hL : ∀ H' : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H' →
      ∀ A, Tendsto (fun n => ustCylinder (H' n) A ∅) atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  obtain ⟨μ, hμ, _⟩ := exists_finiteUST_limit_of_inclusion_limits H (hne H hH) L (hL H hH)
  refine ⟨μ, (fun e => measurable_pi_apply e), ?_⟩
  intro H' hH' A B
  have hw : Tendsto (fun n => finiteUSTProbabilityMeasure (H' n) (hne H' hH' n))
      atTop (𝓝 μ) := by
    apply BinaryLaw.tendsto_iff_positiveCylinders.mpr
    intro C
    simpa only [finiteUSTProbabilityMeasure, ProbabilityMeasure.coe_mk,
      finiteUSTMeasure_positiveCylinder, hμ C] using hL H' hH' C
  have hc := BinaryLaw.tendsto_iff_signedCylinders.mp hw A B
  change Tendsto (fun n => finiteUSTMeasure (H' n) (edgeCylinder A B)) atTop
    (𝓝 ((μ : Measure EdgeConfiguration) (edgeCylinder A B))) at hc
  simp only [finiteUSTMeasure_edgeCylinder] at hc
  exact hc

end Problem336

end

end OAI
