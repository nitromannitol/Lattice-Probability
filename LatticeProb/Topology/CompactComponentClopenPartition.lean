import Mathlib.Topology.Separation.Profinite

/-!
# Clopen partitions separating components

A finite nonempty family of distinct components of a compact Hausdorff space can be
separated by a clopen partition, even when the space has infinitely many components.
-/

open Set

namespace LatticeProb.Topology

/-- A finite nonempty family of distinct components admits a clopen partition whose pieces
contain the chosen points. -/
theorem exists_clopen_partition_of_distinct_components
    {X I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Finite I] [Nonempty I] (x : I → X)
    (hx : Function.Injective (fun i => ConnectedComponents.mk (x i))) :
    ∃ C : I → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, x i ∈ C i) ∧
      (⋃ i, C i) = univ ∧ univ.PairwiseDisjoint C := by
  let Z : I → Set (ConnectedComponents X) := fun i => {ConnectedComponents.mk (x i)}
  let D : I → Set (ConnectedComponents X) := fun _ => univ
  have hZ : ∀ i, IsClosed (Z i) := fun _ => isClosed_singleton
  have hD : ∀ i, IsClopen (D i) := fun _ => isClopen_univ
  have hZD : ∀ i, Z i ⊆ D i := fun _ => subset_univ _
  have hdis : univ.PairwiseDisjoint Z := by
    intro i _ j _ hij
    apply disjoint_singleton.mpr
    exact fun h => hij (hx h)
  obtain ⟨V, hV, hZV, _, hcover, hVdis⟩ :=
    exists_clopen_partition_of_clopen_cover hZ hD hZD hdis
  refine ⟨fun i => ConnectedComponents.mk ⁻¹' V i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hV i).preimage ConnectedComponents.continuous_coe
  · intro i
    exact hZV i (mem_singleton _)
  · apply eq_univ_of_forall
    intro y
    apply mem_iUnion.mpr
    have hy : ConnectedComponents.mk y ∈ ⋃ i, D i := by
      obtain ⟨i⟩ := ‹Nonempty I›
      exact mem_iUnion.mpr ⟨i, mem_univ _⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hy)
    exact ⟨i, hi⟩
  · intro i hi j hj hij
    exact (hVdis hi hj hij).preimage _

end LatticeProb.Topology
