import LatticeProb.Topology.FiniteCompactComponentContainment

/-! # Finite collections of non-singleton compact components -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- Finitely many distinct non-singleton components can be witnessed by
connected compact subsets of disjoint compact pieces, with a compact residual. -/
theorem finite_nonsubsingleton_components_iff_compact_partition
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X}
    (hS : IsCompact S) (n : ℕ) :
    (∃ x : Fin n → X, (∀ i, x i ∈ S) ∧
      Function.Injective (fun i => connectedComponentIn S (x i)) ∧
      ∀ i, ¬ (connectedComponentIn S (x i)).Subsingleton) ↔
    ∃ (P W : Fin n → Set X) (R : Set X),
      IsCompact R ∧ (∀ i, IsCompact (P i)) ∧
      (∀ i, Disjoint (P i) R) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) ∪ R = S ∧
      ∀ i, IsCompact (W i) ∧ IsConnected (W i) ∧ W i ⊆ P i ∧
        ¬ (W i).Subsingleton := by
  classical
  constructor
  · rintro ⟨x, hx, hinj, hn⟩
    let t : Finset X := Finset.univ.image x
    have hxt : ∀ i, x i ∈ t := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have htS : ∀ z ∈ t, z ∈ S := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact hx i
    have ht : ∀ z ∈ t, ∀ w ∈ t, z ≠ w →
        connectedComponentIn S z ≠ connectedComponentIn S w := by
      intro z hz w hw hzw heq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      exact hzw (congrArg x (hinj heq))
    obtain ⟨P, R, hR, hP, hcontain, hPR, hPP, hcover⟩ :=
      exists_compact_partition_containing_finite_components hS t htS ht
    refine ⟨fun i => P (x i), fun i => connectedComponentIn S (x i), R,
      hR, (fun i => hP _ (hxt i)), (fun i => hPR _ (hxt i)), ?_, ?_, ?_⟩
    · intro i j hij
      apply hPP _ (hxt i) _ (hxt j)
      intro heq
      exact hij (hinj (congrArg (connectedComponentIn S) heq))
    · have hpi : (⋃ i, P (x i)) = ⋃ z ∈ (t : Set X), P z := by
        ext z
        simp only [mem_iUnion, Finset.mem_coe, t, Finset.mem_image,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨x i, ⟨i, rfl⟩, hi⟩
        · rintro ⟨_, ⟨i, rfl⟩, hi⟩
          exact ⟨i, hi⟩
      rw [hpi, hcover]
    · intro i
      have hc : IsClosed (connectedComponentIn S (x i)) := by
        apply closure_subset_iff_isClosed.mp
        apply IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn.closure
        · exact subset_closure (mem_connectedComponentIn (hx i))
        · exact closure_minimal (connectedComponentIn_subset S (x i)) hS.isClosed
      exact ⟨hS.of_isClosed_subset hc (connectedComponentIn_subset S (x i)),
        isConnected_connectedComponentIn_iff.mpr (hx i), hcontain _ (hxt i), hn i⟩
  · rintro ⟨P, W, R, hR, hP, hPR, hPP, hcover, hW⟩
    choose x hx using fun i => (hW i).2.1.nonempty
    have hPS : ∀ i, P i ⊆ S := by
      intro i z hz
      rw [← hcover]
      exact Or.inl (mem_iUnion.mpr ⟨i, hz⟩)
    have hxS : ∀ i, x i ∈ S := fun i => hPS i ((hW i).2.2.1 (hx i))
    have hsub : ∀ i, W i ⊆ connectedComponentIn S (x i) := by
      intro i
      exact (hW i).2.1.isPreconnected.subset_connectedComponentIn (hx i)
        ((hW i).2.2.1.trans (hPS i))
    refine ⟨x, hxS, ?_, fun i h => (hW i).2.2.2 (h.anti (hsub i))⟩
    intro i j heq
    by_contra hij
    let B : Set X := (⋃ k ∈ ((Finset.univ.erase i : Finset (Fin n)) : Set (Fin n)), P k) ∪ R
    have hB : IsCompact B := (Finset.univ.erase i).isCompact_biUnion (by
      intro k hk
      exact hP k) |>.union hR
    have hdis : Disjoint (P i) B := by
      rw [disjoint_union_right, disjoint_iUnion_right]
      refine ⟨?_, hPR i⟩
      intro k
      rw [disjoint_iUnion_right]
      intro hk
      exact hPP i k (Finset.ne_of_mem_erase hk).symm
    have hU : P i ∪ B = S := by
      ext z
      rw [← hcover]
      simp only [B, mem_union, mem_iUnion, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro (hz | ⟨k, hk, hz⟩ | hz)
        · exact Or.inl ⟨i, hz⟩
        · exact Or.inl ⟨k, hz⟩
        · exact Or.inr hz
      · rintro (⟨k, hz⟩ | hz)
        · by_cases hki : k = i
          · subst k; exact Or.inl hz
          · exact Or.inr (Or.inl ⟨k, hki, hz⟩)
        · exact Or.inr (Or.inr hz)
    have hxPi : x i ∈ P i := (hW i).2.2.1 (hx i)
    have hxjB : x j ∈ B := Or.inl (mem_iUnion.mpr ⟨j,
      mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩, (hW j).2.2.1 (hx j)⟩⟩)
    have hnot := (not_mem_component_iff_compact_partition hS (hxS i) (hxS j)).mpr
      ⟨P i, B, hP i, hB, hdis, hU, hxPi, hxjB⟩
    apply hnot
    change connectedComponentIn S (x i) = connectedComponentIn S (x j) at heq
    rw [heq]
    exact mem_connectedComponentIn (hxS j)

end LatticeProb.Topology
