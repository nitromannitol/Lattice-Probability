/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/CriticalPercolation/Clusters/ClusterTail.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ClusterTail in place of OAI.Probability.CriticalPercolation.Clusters.ClusterTail, and the module paths of local imports are changed in the same way;
   the unused declarations `lowerSemicontinuous_real_clusterTail`, `subcritical_uniform_clusterTail` (they need modules not copied here) are omitted; statements and proofs of the declarations kept are unchanged. -/
import Mathlib
import LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterTail (o : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster ω o ∧ n ≤ K.ncard}

lemma clusterTail_isUpperSet (o : V) (n : ℕ) : IsUpperSet (G.clusterTail o n) := by
  rintro ω ω' h ⟨K, hK, hKω, hn⟩
  exact ⟨K, hK, hKω.trans (G.cluster_mono h o), hn⟩

lemma clusterTail_hasFiniteOpenWitness (o : V) (n : ℕ) :
    BernoulliProduct.HasFiniteOpenWitness (G.clusterTail o n) := by
  rintro ω ⟨K, hK, hKω, hn⟩
  obtain ⟨s, hs, hsω, hKs⟩ := G.finite_subset_cluster_finite_witness hK hKω
  exact ⟨s, hs, hsω, K, hK, hKs, hn⟩

lemma measurableSet_clusterTail [Countable E] (o : V) (n : ℕ) :
    MeasurableSet (G.clusterTail o n) :=
  BernoulliProduct.measurableSet_finiteWitness _ (G.clusterTail_isUpperSet o n)
    (G.clusterTail_hasFiniteOpenWitness o n)

lemma clusterTail_antitone (o : V) : Antitone (G.clusterTail o) := by
  rintro m n h ω ⟨K, hK, hKω, hn⟩
  exact ⟨K, hK, hKω, h.trans hn⟩

lemma infiniteEvent_subset_clusterTail (o : V) (n : ℕ) :
    G.infiniteEvent o ⊆ G.clusterTail o n := by
  intro ω hω
  obtain ⟨K, hKω, hK, hn⟩ := hω.exists_subset_ncard_eq n
  exact ⟨K, hK, hKω, hn.ge⟩

lemma infiniteEvent_eq_iInter_clusterTail (o : V) :
    G.infiniteEvent o = ⋂ n, G.clusterTail o n := by
  apply Set.Subset.antisymm
  · exact Set.subset_iInter fun n => G.infiniteEvent_subset_clusterTail o n
  · intro ω hω
    change (G.cluster ω o).Infinite
    intro hfin
    obtain ⟨K, hK, hKω, hn⟩ := Set.mem_iInter.mp hω ((G.cluster ω o).ncard + 1)
    have hle := Set.ncard_le_ncard hKω hfin
    omega

lemma tendsto_real_clusterTail [Countable E] (p : unitInterval) (o : V) :
    Tendsto (fun n => (G.law p).real (G.clusterTail o n)) atTop
      (𝓝 ((G.law p).real (G.infiniteEvent o))) := by
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (G.measurableSet_clusterTail o n).nullMeasurableSet)
    (G.clusterTail_antitone o)
    ⟨0, measure_ne_top _ _⟩
  rw [← G.infiniteEvent_eq_iInter_clusterTail o] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h


lemma Aut.preimage_clusterTail (φ : G.Aut) (o : V) (n : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.clusterTail (φ.vertex o) n =
      G.clusterTail o n := by
  ext ω
  simp only [Set.mem_preimage, clusterTail, Set.mem_ofPred_eq]
  rw [← φ.cluster_image]
  constructor
  · rintro ⟨K, hK, hKω, hn⟩
    refine ⟨φ.vertex.symm '' K, hK.image _, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hKω hv
      simpa using hw
    · rwa [Set.ncard_image_of_injective _ φ.vertex.symm.injective]
  · rintro ⟨K, hK, hKω, hn⟩
    exact ⟨φ.vertex '' K, hK.image _, Set.image_mono hKω,
      by rwa [Set.ncard_image_of_injective _ φ.vertex.injective]⟩

lemma Aut.clusterTail_real [Countable E] (φ : G.Aut) (p : unitInterval) (o : V) (n : ℕ) :
    (G.law p).real (G.clusterTail (φ.vertex o) n) = (G.law p).real (G.clusterTail o n) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_clusterTail _ _), φ.preimage_clusterTail]


lemma tendsto_real_clusterTail_subcritical [Countable V] [Countable E]
    {p : unitInterval} (hp : p < G.criticalProbability) (o : V) :
    Tendsto (fun n => (G.law p).real (G.clusterTail o n)) atTop (𝓝 0) := by
  have hz : G.law p (G.infiniteEvent o) = 0 := by
    exact measure_mono_null (show G.infiniteEvent o ⊆ G.percolates from
      fun ω hω => ⟨o, hω⟩) (G.law_percolates_eq_zero_of_lt_critical hp)
  simpa only [measureReal_def, hz, ENNReal.toReal_zero] using G.tendsto_real_clusterTail p o

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
