import LatticeProb.Topology.UniqueBoundedComplementFill
import LatticeProb.Topology.CompactSplit

/-! # Contact components and the boundary of a unique hole -/

open Set Metric Bornology

namespace LatticeProb.Topology

/-- If a compact set and a nonempty closed set have preconnected union, every component
of the compact set meets the closed set. -/
theorem connectedComponentIn_inter_nonempty_of_union_preconnected
    {X : Type*} [TopologicalSpace X] [T2Space X] {T F : Set X}
    (hT : IsCompact T) (hF : IsClosed F) (hFn : F.Nonempty)
    (hTF : IsPreconnected (T ∪ F)) {x : X} (hx : x ∈ T) :
    (connectedComponentIn T x ∩ F).Nonempty := by
  by_contra h
  have hdis : Disjoint (connectedComponentIn T x) F := disjoint_left.mpr (by
    intro y hyT hyF
    exact h ⟨y, hyT, hyF⟩)
  obtain ⟨P, Q, hP, hQ, hPQ, hcover, hPF, hQx⟩ :=
    exists_compact_split hT isClosed_singleton hF (by
      intro S hST hSc hmeet
      obtain ⟨⟨y, hyS, hyx⟩, z, hzS, hzF⟩ := hmeet
      have hxS : x ∈ S := by
        have hy : y = x := mem_singleton_iff.mp hyx
        simpa only [hy] using hyS
      exact disjoint_left.mp hdis (hSc.subset_connectedComponentIn hxS hST hzS) hzF)
  have hxP : x ∈ P := by
    have : x ∈ P ∪ Q := hcover ▸ hx
    rcases this with hp | hq
    · exact hp
    · exact False.elim (disjoint_left.mp hQx hq (mem_singleton x))
  have hsub : T ∪ F ⊆ P ∪ (Q ∪ F) := by
    intro z hz
    rcases hz with hzT | hzF
    · rw [← hcover] at hzT
      rcases hzT with hp | hq
      · exact Or.inl hp
      · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr hzF)
  have hmeet := isPreconnected_closed_iff.mp hTF P (Q ∪ F) hP.isClosed
    (hQ.isClosed.union hF) hsub ⟨x, Or.inl hx, hxP⟩
    (by obtain ⟨y, hy⟩ := hFn; exact ⟨y, Or.inr hy, Or.inr hy⟩)
  obtain ⟨y, _, hyP, hyQF⟩ := hmeet
  rcases hyQF with hyQ | hyF
  · exact disjoint_left.mp hPQ hyP hyQ
  · exact disjoint_left.mp hPF hyP hyF

/-- Every component of the intersection is incident to the unique bounded complementary
component of the union. -/
theorem contact_component_meets_frontier_of_unique_bounded_component
    {A B U : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsConnected A) (hBc : IsConnected B)
    (hAcom : IsPreconnected Aᶜ) (hAu : ¬ IsBounded Aᶜ)
    (hBcom : IsPreconnected Bᶜ) (hBu : ¬ IsBounded Bᶜ)
    (hU : U ∈ connectedComponentsIn (A ∪ B)ᶜ) (hUb : IsBounded U)
    (huniq : ∀ V ∈ connectedComponentsIn (A ∪ B)ᶜ, IsBounded V → V = U)
    {x : ℂ} (hx : x ∈ A ∩ B) :
    (connectedComponentIn (A ∩ B) x ∩ frontier U).Nonempty := by
  have hF : (frontier U ∩ B).Nonempty :=
    (frontier_inter_nonempty_of_bounded_compl_component hA.isClosed hB.isClosed
      hAcom hAu hBcom hBu hU hUb).2
  have h := connectedComponentIn_inter_nonempty_of_union_preconnected
    (hA.inter_right hB.isClosed) (isClosed_frontier.inter hB.isClosed) hF
    (isPreconnected_inter_union_frontier_of_unique_bounded_component
      hA hB hAc hBc hAcom hAu hBcom hBu hU hUb huniq) hx
  obtain ⟨y, hy, hyF, _⟩ := h
  exact ⟨y, hy, hyF⟩

end LatticeProb.Topology
