import LatticeProb.Topology.CompactPlaneIntersection
import LatticeProb.Topology.BoundedComplementFrontier

/-! # Filling a unique bounded complementary component -/

open Set Metric Bornology

namespace LatticeProb.Topology

/-- Filling the unique bounded complementary component of a compact plane set leaves a
preconnected complement. -/
theorem isPreconnected_compl_union_closure_of_unique_bounded_component {K U : Set ℂ}
    (hK : IsCompact K) (hU : U ∈ connectedComponentsIn Kᶜ) (hUb : IsBounded U)
    (huniq : ∀ V ∈ connectedComponentsIn Kᶜ, IsBounded V → V = U) :
    IsPreconnected (K ∪ closure U)ᶜ := by
  obtain ⟨p, hp, _, hchar⟩ := exists_unbounded_compl_component hK
  have hUo := isOpen_of_mem_connectedComponentsIn_compl hK.isClosed hU
  have hfr := frontier_subset_of_mem_connectedComponentsIn_compl hK.isClosed hU
  have hclosure : closure U ⊆ U ∪ K := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · apply Or.inr
      apply hfr
      rw [hUo.frontier_eq]
      exact ⟨hx, hxU⟩
  have heq : (K ∪ closure U)ᶜ = connectedComponentIn Kᶜ p := by
    ext x
    constructor
    · intro hx
      have hxK : x ∈ Kᶜ := fun hxK => hx (Or.inl hxK)
      apply (hchar x hxK).2
      intro hb
      have hmem : connectedComponentIn Kᶜ x ∈ connectedComponentsIn Kᶜ := by
        exact ⟨x, hxK, rfl⟩
      have heqU := huniq _ hmem hb
      have hxU : x ∈ U := heqU ▸ mem_connectedComponentIn hxK
      exact hx (Or.inr (subset_closure hxU))
    · intro hx
      have hxK : x ∈ Kᶜ := connectedComponentIn_subset _ _ hx
      intro hxKC
      rcases hxKC with hxKmem | hxC
      · exact hxK hxKmem
      · rcases hclosure hxC with hxU | hxKmem
        · have heqU : connectedComponentIn Kᶜ x = U := by
            obtain ⟨y, hy, hyU⟩ := hU
            rw [← hyU] at hxU ⊢
            exact (connectedComponentIn_eq hxU).symm
          have hb : IsBounded (connectedComponentIn Kᶜ x) := heqU ▸ hUb
          exact ((hchar x hxK).1 hx) hb
        · exact hxK hxKmem
  rw [heq]
  exact isPreconnected_connectedComponentIn


/-- Filling the unique bounded component joins the original intersection to the part of
its boundary lying in the second set. -/
theorem isPreconnected_inter_union_frontier_of_unique_bounded_component
    {A B U : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsConnected A) (hBc : IsConnected B)
    (hAcom : IsPreconnected Aᶜ) (hAu : ¬ IsBounded Aᶜ)
    (hBcom : IsPreconnected Bᶜ) (hBu : ¬ IsBounded Bᶜ)
    (hU : U ∈ connectedComponentsIn (A ∪ B)ᶜ) (hUb : IsBounded U)
    (huniq : ∀ V ∈ connectedComponentsIn (A ∪ B)ᶜ, IsBounded V → V = U) :
    IsPreconnected ((A ∩ B) ∪ (frontier U ∩ B)) := by
  have hUo := isOpen_of_mem_connectedComponentsIn_compl (hA.union hB).isClosed hU
  have hUsub := subset_of_mem_connectedComponentsIn hU
  obtain ⟨⟨x, hxfr, hxA⟩, _⟩ :=
    frontier_inter_nonempty_of_bounded_compl_component hA.isClosed hB.isClosed
      hAcom hAu hBcom hBu hU hUb
  have hconnected : IsConnected (A ∪ closure U) :=
    hAc.union ⟨x, hxA, frontier_subset_closure hxfr⟩
      (isConnected_of_mem_connectedComponentsIn hU).closure
  have hcom : IsPreconnected ((A ∪ closure U) ∪ B)ᶜ := by
    have h := isPreconnected_compl_union_closure_of_unique_bounded_component
      (hA.union hB) hU hUb huniq
    simpa only [union_assoc, union_comm, union_left_comm] using h
  have hinter := isPreconnected_inter_of_compl_union_preconnected
    (hA.union hUb.isCompact_closure) hB hconnected hBc hcom
  have heq : (A ∪ closure U) ∩ B = (A ∩ B) ∪ (frontier U ∩ B) := by
    ext y
    constructor
    · rintro ⟨hyA | hyU, hyB⟩
      · exact Or.inl ⟨hyA, hyB⟩
      · apply Or.inr
        refine ⟨?_, hyB⟩
        rw [hUo.frontier_eq]
        exact ⟨hyU, fun hy => hUsub hy (Or.inr hyB)⟩
    · rintro (⟨hyA, hyB⟩ | ⟨hyU, hyB⟩)
      · exact ⟨Or.inl hyA, hyB⟩
      · exact ⟨Or.inr (frontier_subset_closure hyU), hyB⟩
  rwa [heq] at hinter

end LatticeProb.Topology
