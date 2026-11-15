import LatticeProb.Topology.FiniteClosedComponentPartition

/-! # Counting non-singleton pieces of finite closed partitions -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb

/-- The non-singleton components of a finite disjoint closed preconnected
partition are counted by its non-singleton pieces. -/
theorem ncard_nonSingletonComponents_eq_card_nonSingleton_pieces
    {X ι : Type*} [TopologicalSpace X] [Finite ι] (K : ι → Set X) (p : ι → X)
    (hp : ∀ i, p i ∈ K i) (hclosed : ∀ i, IsClosed (K i))
    (hconn : ∀ i, IsPreconnected (K i))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    {C ∈ connectedComponentIn (⋃ i, K i) '' (⋃ i, K i) | ¬ C.Subsingleton}.ncard =
      Nat.card {i // ¬ (K i).Subsingleton} := by
  classical
  let J := {i // ¬ (K i).Subsingleton}
  apply ncard_nonSingletonComponents_eq_card_witnesses (⋃ i, K i)
    (fun i : J => K i.1) (fun i => p i.1) (fun i => hp i.1)
    (fun i => hconn i.1) (fun i => subset_iUnion K i.1) (fun i => i.2)
  · intro i j hij
    have heq : K i.1 = K j.1 := by
      simpa only [connectedComponentIn_eq_of_finite_closed_partition K hclosed hconn hdisj
        (hp i.1), connectedComponentIn_eq_of_finite_closed_partition K hclosed hconn hdisj
        (hp j.1)] using hij
    apply Subtype.ext
    by_contra hne
    exact disjoint_left.mp (hdisj hne) (hp i.1) (heq ▸ hp i.1)
  · intro x hx hn
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have heq := connectedComponentIn_eq_of_finite_closed_partition K hclosed hconn hdisj hi
    have hni : ¬ (K i).Subsingleton := by
      rw [← heq]
      exact hn
    exact ⟨⟨i, hni⟩, heq.symm.subset⟩

end LatticeProb
