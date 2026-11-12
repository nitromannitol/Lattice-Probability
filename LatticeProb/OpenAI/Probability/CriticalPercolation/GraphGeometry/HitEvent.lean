/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/CriticalPercolation/GraphGeometry/HitEvent.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.HitEvent in place of OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent, and the module paths of local imports are changed in the same way; the import of LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.HitValue, LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.RestrictVertices (not copied here) is replaced by the imports of the copied modules it reaches,
   namely LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure, LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.VertexBall, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Density, LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ComponentSelf, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Distribution;
   the unused declarations `expect_hit_eq_real`, `expect_jointHit_eq_real`, `finite_edge_joint_gluing_law`, `finite_subgraph_joint_gluing`, `countable_joint_gluing_finite`, `countable_joint_gluing`, `joint_gluing` (they need modules not copied here) are omitted and `CriticalPercolation.ClusterColumns`, a namespace of modules not copied here, is removed from `open` commands; statements and proofs of the declarations kept are unchanged. -/
import Mathlib
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import LatticeProb.OpenAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Density
import LatticeProb.OpenAI.Probability.CriticalPercolation.Clusters.ComponentSelf
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Distribution

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def hitEvent (o : V) (A : Set V) : Set (Set E) :=
  {ω | (G.cluster ω o ∩ A).Nonempty}

lemma measurableSet_hitEvent [Countable V] [Countable E] (o : V) (A : Set V) :
    MeasurableSet (G.hitEvent o A) := by
  exact (Measurable.exists fun v => (G.measurable_reachable o v).and measurable_const).setOf

lemma hitEvent_mono_edges (o : V) (A : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    ω ∈ G.hitEvent o A → ω' ∈ G.hitEvent o A :=
  fun hω => hω.mono (Set.inter_subset_inter_left A (G.cluster_mono h o))

lemma hitEvent_mono_target (o : V) {A A' : Set V} (h : A ⊆ A') :
    G.hitEvent o A ⊆ G.hitEvent o A' :=
  fun _ hω => hω.mono (Set.inter_subset_inter_right _ h)




def restrictEdges (s : Set E) : BondGraph V s where
  ends e := G.ends e

lemma restrictEdges_openGraph (s : Set E) (ω : Set E) :
    (G.restrictEdges s).openGraph (Subtype.val ⁻¹' ω) = G.openGraph (s ∩ ω) := by
  unfold openGraph restrictEdges
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists]
  constructor
  · rintro ⟨e, hs, hω, rfl⟩
    exact ⟨e, ⟨hs, hω⟩, rfl⟩
  · rintro ⟨e, ⟨hs, hω⟩, rfl⟩
    exact ⟨e, hs, hω, rfl⟩

lemma restrictEdges_hitEvent (s : Set E) (o : V) (A : Set V) :
    (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        ((G.restrictEdges s).hitEvent o A) =
      {ω | s ∩ ω ∈ G.hitEvent o A} := by
  ext ω
  simp only [Set.mem_preimage, hitEvent, cluster, Set.mem_ofPred_eq,
    G.restrictEdges_openGraph]


lemma finite_subset_exhaustion {X : Type*} {U S : Set X}
    (K : Set.FiniteExhaustion U) (hS : S.Finite) (hSU : S ⊆ U) :
    ∃ n, S ⊆ K n := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x S hx hS ih =>
      obtain ⟨n, hn⟩ := ih (Set.Subset.trans (Set.subset_insert _ _) hSU)
      have hxU := hSU (Set.mem_insert x S)
      rw [← K.iUnion_eq, Set.mem_iUnion] at hxU
      obtain ⟨m, hm⟩ := hxU
      exact ⟨max m n, Set.insert_subset (K.mono (le_max_left _ _) hm)
        (Set.Subset.trans hn (K.mono (le_max_right _ _)))⟩

lemma hitEvent_exhaustion (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) = G.hitEvent o A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact G.hitEvent_mono_edges o A Set.inter_subset_right hn
  · rintro ⟨v, hv, hvA⟩
    obtain ⟨s, hs, hsω, hvs⟩ := G.mem_cluster_finite_witness hv
    obtain ⟨n, hn⟩ := finite_subset_exhaustion K hs (Set.subset_univ s)
    exact Set.mem_iUnion.mpr ⟨n, v, G.cluster_mono
      (Set.subset_inter hn hsω) o hvs, hvA⟩

lemma hitEvent_exhaustion_mono (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Monotone (fun n => {ω | K n ∩ ω ∈ G.hitEvent o A}) := by
  intro m n h ω hω
  exact G.hitEvent_mono_edges o A (Set.inter_subset_inter_left _ (K.mono h)) hω

lemma tendsto_real_hitEvent_exhaustion [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Tendsto (fun n => (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A})
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A))) := by
  have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
    (G.hitEvent_exhaustion_mono K o A)
  rw [G.hitEvent_exhaustion K o A] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma jointHitEvent_exhaustion (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    (⋃ n, ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩
      {ω | K n ∩ ω ∈ G.hitEvent o T})) = G.hitEvent o A ∩ G.hitEvent o T := by
  calc
    _ = (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) ∩
        (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o T}) :=
      Set.iUnion_inter_of_monotone (G.hitEvent_exhaustion_mono K o A)
        (G.hitEvent_exhaustion_mono K o T)
    _ = _ := by rw [G.hitEvent_exhaustion K o A, G.hitEvent_exhaustion K o T]

lemma tendsto_real_jointHitEvent_exhaustion [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    Tendsto (fun n => (BernoulliProduct.law q).real
      ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩ {ω | K n ∩ ω ∈ G.hitEvent o T}))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T))) := by
  have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
    ((G.hitEvent_exhaustion_mono K o A).inter (G.hitEvent_exhaustion_mono K o T))
  rw [G.jointHitEvent_exhaustion K o A T] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma finite_sum_abs_sub_bound {X : Type*} [Fintype X] (f g : X → ℝ) (x : X) :
    |f x - g x| ≤ ∑ y, |f y - g y| := by
  exact Finset.single_le_sum (fun y _ => abs_nonneg (f y - g y)) (Finset.mem_univ x)


lemma hitEvent_iUnion {I : Type*} (o : V) (A : I → Set V) :
    G.hitEvent o (⋃ i, A i) = ⋃ i, G.hitEvent o (A i) := by
  ext ω
  simp only [hitEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.nonempty_def,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨v, hv, i, hi⟩
    exact ⟨i, v, hv, hi⟩
  · rintro ⟨i, v, hv, hi⟩
    exact ⟨v, hv, i, hi⟩



end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
