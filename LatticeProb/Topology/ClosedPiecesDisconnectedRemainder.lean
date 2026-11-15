import LatticeProb.Topology.ConnectedWitnessComponentCount
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Components of closed pieces and a totally disconnected remainder -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb

private theorem component_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    {x : X} (hx : x ∈ A) : connectedComponentIn (A ∪ B) x ⊆ A := by
  have hc : connectedComponentIn (A ∪ B) x ⊆ A ∪ B :=
    connectedComponentIn_subset _ _
  have he : connectedComponentIn (A ∪ B) x ∩ (A ∩ B) = ∅ := by
    rw [disjoint_iff_inter_eq_empty.mp hAB, inter_empty]
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp
    isPreconnected_connectedComponentIn A B hA hB hc he with h | h
  · exact h
  · exact False.elim (disjoint_left.mp hAB hx (h (mem_connectedComponentIn (Or.inl hx))))

/-- A finite family of disjoint closed nontrivial preconnected pieces accounts for
all nontrivial components when the remaining closed set is totally disconnected. -/
theorem ncard_nonSingletonComponents_eq_card_of_disconnected_remainder
    {X ι : Type*} [TopologicalSpace X] [Finite ι] (K : ι → Set X) (R : Set X)
    (p : ι → X) (hp : ∀ i, p i ∈ K i) (hclosed : ∀ i, IsClosed (K i))
    (hconn : ∀ i, IsPreconnected (K i)) (hn : ∀ i, ¬ (K i).Subsingleton)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hR : IsClosed R) (hRdis : ∀ i, Disjoint (K i) R)
    (hRtot : IsTotallyDisconnected R) :
    {C ∈ connectedComponentIn ((⋃ i, K i) ∪ R) '' ((⋃ i, K i) ∪ R) |
      ¬ C.Subsingleton}.ncard = Nat.card ι := by
  classical
  let S := (⋃ i, K i) ∪ R
  have hKi (i : ι) {x : X} (hx : x ∈ K i) : connectedComponentIn S x = K i := by
    let T : Set X := (⋃ j : {j // j ≠ i}, K j.1) ∪ R
    have hT : IsClosed T := (isClosed_iUnion_of_finite (fun j : {j // j ≠ i} => hclosed j.1)).union hR
    have hKT : Disjoint (K i) T := by
      apply disjoint_left.mpr
      intro y hy hyT
      rcases hyT with hyT | hyR
      · obtain ⟨j, hyj⟩ := mem_iUnion.mp hyT
        exact disjoint_left.mp (hdisj (Ne.symm j.2)) hy hyj
      · exact disjoint_left.mp (hRdis i) hy hyR
    have hST : S = K i ∪ T := by
      ext y
      simp only [S, T, mem_union, mem_iUnion]
      constructor
      · rintro (⟨j, hj⟩ | hy)
        · by_cases hji : j = i
          · exact Or.inl (hji ▸ hj)
          · exact Or.inr (Or.inl ⟨⟨j, hji⟩, hj⟩)
        · exact Or.inr (Or.inr hy)
      · rintro (hy | ⟨j, hy⟩ | hy)
        · exact Or.inl ⟨i, hy⟩
        · exact Or.inl ⟨j.1, hy⟩
        · exact Or.inr hy
    have hsub : K i ⊆ S := fun _ hy => Or.inl (mem_iUnion.mpr ⟨i, hy⟩)
    apply Subset.antisymm
    · rw [hST]
      exact component_subset_left (hclosed i) hT hKT hx
    · exact (hconn i).subset_connectedComponentIn hx hsub
  have hRS : ∀ x ∈ R, connectedComponentIn S x ⊆ R := by
    intro x hx
    have hclosedU : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hclosed
    have hd : Disjoint R (⋃ i, K i) := by
      apply disjoint_left.mpr
      intro y hyR hyU
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hyU
      exact disjoint_left.mp (hRdis i) hyi hyR
    have heq : S = R ∪ ⋃ i, K i := union_comm _ _
    rw [heq]
    exact component_subset_left hR hclosedU hd hx
  apply ncard_nonSingletonComponents_eq_card_witnesses S K p hp hconn
    (fun i _ hy => Or.inl (mem_iUnion.mpr ⟨i, hy⟩)) hn
  · intro i j hij
    have heq : K i = K j := by simpa only [hKi i (hp i), hKi j (hp j)] using hij
    by_contra hne
    exact disjoint_left.mp (hdisj hne) (hp i) (heq ▸ hp i)
  · intro x hx hnon
    rcases hx with hx | hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨i, (hKi i hi).symm.subset⟩
    · exact False.elim (hnon (hRtot _ (hRS x hx) isPreconnected_connectedComponentIn))

end LatticeProb
