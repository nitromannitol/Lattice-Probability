import LatticeProb.Topology.IntersectionHoleExistence
import LatticeProb.Topology.UniqueHoleContactIncidence

/-! # Bounded holes from disconnected intersections -/

open Set Bornology

namespace LatticeProb.Topology

/-- Distinct components of the intersection force a bounded complementary component. -/
theorem exists_bounded_compl_component_of_not_mem_inter_component {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B) (hAc : IsConnected A) (hBc : IsConnected B)
    {x y : ℂ} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B)
    (hxy : y ∉ connectedComponentIn (A ∩ B) x) :
    ∃ U ∈ connectedComponentsIn (A ∪ B)ᶜ, IsBounded U := by
  by_contra h
  have he : IsEmpty (BoundedPlaneComplementComponent (A ∪ B)) :=
    ⟨fun U => by
      obtain ⟨z, hz, hU⟩ := U.1.2
      exact h ⟨U.1.1, ⟨z, hz, hU.symm⟩, U.2⟩⟩
  have hp := isPreconnected_inter_of_compl_union_preconnected hA hB hAc hBc
    (isPreconnected_compl_of_no_bounded_components (hA.union hB) he)
  exact hxy (hp.subset_connectedComponentIn hx Subset.rfl hy)

/-- For a disconnected intersection and at most one bounded complementary component,
there is a unique bounded component and every contact component meets its frontier. -/
theorem exists_unique_bounded_compl_component_with_contact_frontier {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hAcom : IsPreconnected Aᶜ) (hBcom : IsPreconnected Bᶜ)
    (huniq : ∀ U ∈ connectedComponentsIn (A ∪ B)ᶜ,
      ∀ V ∈ connectedComponentsIn (A ∪ B)ᶜ, IsBounded U → IsBounded V → U = V)
    {x y : ℂ} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B)
    (hxy : y ∉ connectedComponentIn (A ∩ B) x) :
    ∃ U ∈ connectedComponentsIn (A ∪ B)ᶜ, IsBounded U ∧
      (∀ V ∈ connectedComponentsIn (A ∪ B)ᶜ, IsBounded V → V = U) ∧
      (∀ z ∈ A ∩ B, (connectedComponentIn (A ∩ B) z ∩ frontier U).Nonempty) := by
  obtain ⟨U, hU, hUb⟩ :=
    exists_bounded_compl_component_of_not_mem_inter_component hA hB hAc hBc hx hy hxy
  have hu : ∀ V ∈ connectedComponentsIn (A ∪ B)ᶜ, IsBounded V → V = U :=
    fun V hV hVb => huniq V hV U hU hVb hUb
  have hAu : ¬ IsBounded Aᶜ := by
    obtain ⟨p, _, hp, _⟩ := exists_unbounded_compl_component hA
    exact fun h => hp (h.subset (connectedComponentIn_subset _ _))
  have hBu : ¬ IsBounded Bᶜ := by
    obtain ⟨p, _, hp, _⟩ := exists_unbounded_compl_component hB
    exact fun h => hp (h.subset (connectedComponentIn_subset _ _))
  exact ⟨U, hU, hUb, hu, fun _ hz =>
    contact_component_meets_frontier_of_unique_bounded_component
      hA hB hAc hBc hAcom hAu hBcom hBu hU hUb hu hz⟩

end LatticeProb.Topology
