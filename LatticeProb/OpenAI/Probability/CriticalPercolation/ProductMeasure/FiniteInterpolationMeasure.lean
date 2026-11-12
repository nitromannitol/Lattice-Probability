/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/CriticalPercolation/ProductMeasure/FiniteInterpolationMeasure.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure in place of OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure, and the module paths of local imports are changed in the same way; the import of LatticeProb.OpenAI.Probability.CriticalPercolation.Criticality.FiniteInterpolationUniform (not copied here) is replaced by the imports of the copied modules it reaches,
   namely LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper, LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ClusterTail, LatticeProb.OpenAI.Probability.CriticalPercolation.Entropy.BinaryLaw, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.ExpectClosedFlip, LatticeProb.OpenAI.Probability.CriticalPercolation.Modular.WeightedCauchy, LatticeProb.OpenAI.Probability.CriticalPercolation.Model, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Delta, LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.SearchTree, LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.ClosedFresh, LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.Link, LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.VertexBall, LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ClusterObject, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Density;
   the unused declarations `finite_interpolation_measure` (they need modules not copied here) are omitted; statements and proofs of the declarations kept are unchanged. -/
import Mathlib
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper
import LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ClusterTail
import LatticeProb.OpenAI.Probability.CriticalPercolation.Entropy.BinaryLaw
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.ExpectClosedFlip
import LatticeProb.OpenAI.Probability.CriticalPercolation.Modular.WeightedCauchy
import LatticeProb.OpenAI.Probability.CriticalPercolation.Model
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Delta
import LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.SearchTree
import LatticeProb.OpenAI.Probability.CriticalPercolation.Exploration.ClosedFresh
import LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.Link
import LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ClusterObject
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Density

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation
namespace BernoulliProduct
variable {E : Type*} [Fintype E]

lemma prob_eq_real (q : E → unitInterval) (A : Set (Set E)) :
    FiniteProduct.prob (fun e => bitWeight (q e)) (fun ω => ω ∈ A) = (law q).real A := by
  rw [real_eq_expect_indicator]
  unfold FiniteProduct.prob
  rfl

end BernoulliProduct
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def twoClusterEvent (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.openGraph ω).Reachable u v} ∩ G.clusterTail u s ∩ G.clusterTail v s

lemma measurableSet_twoClusterEvent [Countable V] [Countable E] (u v : V) (s : ℕ) :
    MeasurableSet (G.twoClusterEvent u v s) := by
  exact ((G.measurable_reachable u v).setOf.compl.inter
    (G.measurableSet_clusterTail u s)).inter (G.measurableSet_clusterTail v s)

lemma clusterTail_iff_card [Fintype V] (ω : Set E) (u : V) (s : ℕ) :
    ω ∈ G.clusterTail u s ↔ s ≤ (G.cluster ω u).toFinset.card := by
  constructor
  · rintro ⟨K,hK,hsub,hs⟩
    exact hs.trans (by simpa only [Set.ncard_eq_toFinset_card'] using Set.ncard_le_ncard hsub)
  · intro hs
    exact ⟨G.cluster ω u, Set.toFinite _, Set.Subset.rfl, by simpa only [Set.ncard_eq_toFinset_card'] using hs⟩

lemma twoClusterEvent_iff_endpoint [Fintype V] (ω : Set E) (u v : V) (s : ℕ) :
    ω ∈ G.twoClusterEvent u v s ↔ BinaryLaw.endpointEvent G u v s ω := by
  simp only [twoClusterEvent, Set.mem_inter_iff, Set.mem_ofPred_eq,
    clusterTail_iff_card, BinaryLaw.endpointEvent, and_assoc]

lemma finite_endpoint_prob [Fintype V] [Fintype E] (p : unitInterval) (u v : V) (s : ℕ) :
    FiniteProduct.prob (fun _ : E => BernoulliProduct.bitWeight p)
      (BinaryLaw.endpointEvent G u v s) = (G.law p).real (G.twoClusterEvent u v s) := by
  rw [law, ← BernoulliProduct.law_const, ← BernoulliProduct.prob_eq_real]
  congr 1
  funext ω
  exact propext (G.twoClusterEvent_iff_endpoint ω u v s).symm


end BondGraph
end CriticalPercolation
end
end
end

end OAI
