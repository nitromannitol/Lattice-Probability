import LatticeProb.Topology.ConnectedWitnessComponentCount
import Mathlib.Topology.Connected.Clopen

/-! # Components of finite closed partitions -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb

/-- A member of a finite disjoint closed preconnected partition is a component. -/
theorem connectedComponentIn_eq_of_finite_closed_partition
    {X ι : Type*} [TopologicalSpace X] [Finite ι] (K : ι → Set X)
    (hclosed : ∀ i, IsClosed (K i)) (hconn : ∀ i, IsPreconnected (K i))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) {i : ι} {x : X} (hx : x ∈ K i) :
    connectedComponentIn (⋃ j, K j) x = K i := by
  classical
  let R : Set X := ⋃ j : {j // j ≠ i}, K j.1
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hclosed j.1)
  have hdis : Disjoint (K i) R := by
    apply disjoint_left.mpr
    intro y hy hyr
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyr
    exact disjoint_left.mp (hdisj (Ne.symm j.2)) hy hyj
  have hcover : (⋃ j, K j) = K i ∪ R := by
    ext y
    simp only [mem_iUnion, mem_union, R]
    constructor
    · rintro ⟨j, hj⟩
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr ⟨⟨j, hji⟩, hj⟩
    · rintro (hy | ⟨j, hy⟩)
      · exact ⟨i, hy⟩
      · exact ⟨j.1, hy⟩
  have hxS : x ∈ ⋃ j, K j := mem_iUnion.mpr ⟨i, hx⟩
  have hC : connectedComponentIn (⋃ j, K j) x ⊆ K i := by
    have hsub : connectedComponentIn (⋃ j, K j) x ⊆ K i ∪ R :=
      hcover ▸ connectedComponentIn_subset (⋃ j, K j) x
    have hempty : connectedComponentIn (⋃ j, K j) x ∩ (K i ∩ R) = ∅ := by
      rw [disjoint_iff_inter_eq_empty.mp hdis, inter_empty]
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp
      isPreconnected_connectedComponentIn (K i) R (hclosed i) hR hsub hempty with h | h
    · exact h
    · exact False.elim (disjoint_left.mp hdis hx (h (mem_connectedComponentIn hxS)))
  exact Subset.antisymm hC ((hconn i).subset_connectedComponentIn hx
    (subset_iUnion K i))

/-- The non-singleton components of a finite disjoint closed preconnected
partition are counted by its pieces when every piece is non-singleton. -/
theorem ncard_nonSingletonComponents_eq_of_finite_closed_partition
    {X ι : Type*} [TopologicalSpace X] [Finite ι] (K : ι → Set X) (p : ι → X)
    (hp : ∀ i, p i ∈ K i) (hclosed : ∀ i, IsClosed (K i))
    (hconn : ∀ i, IsPreconnected (K i)) (hn : ∀ i, ¬ (K i).Subsingleton)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    {C ∈ connectedComponentIn (⋃ i, K i) '' (⋃ i, K i) | ¬ C.Subsingleton}.ncard =
      Nat.card ι := by
  classical
  apply ncard_nonSingletonComponents_eq_card_witnesses (⋃ i, K i) K p hp hconn
    (fun i => subset_iUnion K i) hn
  · intro i j hij
    have heq : K i = K j := by
      simpa only [connectedComponentIn_eq_of_finite_closed_partition K hclosed hconn hdisj
        (hp i), connectedComponentIn_eq_of_finite_closed_partition K hclosed hconn hdisj
        (hp j)] using hij
    by_contra hne
    exact disjoint_left.mp (hdisj hne) (hp i) (heq ▸ hp i)
  · intro x hx _
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, (connectedComponentIn_eq_of_finite_closed_partition K hclosed hconn hdisj hi).symm.subset⟩

end LatticeProb
