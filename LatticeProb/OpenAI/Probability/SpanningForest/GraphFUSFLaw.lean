/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/SpanningForest/GraphFUSFLaw.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.SpanningForest.GraphFUSFLaw in place of OAI.Probability.SpanningForest.GraphFUSFLaw, and the module paths of local imports are changed in the same way; statements and proofs are unchanged. -/
import LatticeProb.OpenAI.Probability.SpanningForest.USTFiniteDeterminantal
import LatticeProb.OpenAI.Probability.SpanningForest.GraphFreeKernel
import LatticeProb.OpenAI.Probability.SpanningForest.FUSFExistenceReduction
import LatticeProb.OpenAI.Probability.SpanningForest.IntrinsicExhaustion
import LatticeProb.OpenAI.Probability.SpanningForest.Exhaustion

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

theorem exists_connectedExhaustion (G : GraphCode)
    (hC : GraphConnected G) (hL : GraphLocallyFinite G) :
    ∃ H : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H := by
  obtain ⟨v, hv⟩ := hC.exists_adj 0
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    simp [Adj, G.2.1 0] at hv
  let e : EdgeCode := ⟨(0, v), Nat.pos_of_ne_zero hv0⟩
  exact ⟨IntrinsicExhaustion.edgeBallSubgraph G hL e,
    IntrinsicExhaustion.isConnectedExhaustion_edgeBallSubgraph hC hL e hv⟩

theorem exists_hasFUSFLaw_of_finite_identity (G : GraphCode)
    (hC : GraphConnected G) (hL : GraphLocallyFinite G)
    (hfinite : ∀ K : FiniteSubgraphCode, IsFiniteConnectedSubgraph G K →
      ∀ A : Finset EdgeCode,
        ustCylinder K A ∅ = FreeKernel.finiteInclusionMinor K A) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  obtain ⟨H, hH⟩ := exists_connectedExhaustion G hC hL
  exact exists_hasFUSFLaw_of_inclusion_limits G H hH
    (FreeKernel.inclusionMinorLimit G)
    (FreeKernel.common_inclusion_limits_of_finite_identity G hfinite)

theorem exists_hasFUSFLaw (G : GraphCode)
    (hC : GraphConnected G) (hL : GraphLocallyFinite G) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  apply exists_hasFUSFLaw_of_finite_identity G hC hL
  intro K hK A
  exact FreeKernel.ustCylinder_eq_finiteKernel_minor hK A

end Problem336

end

end OAI
