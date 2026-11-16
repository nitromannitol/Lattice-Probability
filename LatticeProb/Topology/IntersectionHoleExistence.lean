import LatticeProb.Topology.CompactPlaneIntersection

/-! # Connected intersections and complementary components -/

open Set Bornology

namespace LatticeProb.Topology

/-- For compact connected plane sets with preconnected complements, their intersection is
preconnected exactly when their union has no bounded complementary component. -/
theorem isPreconnected_inter_iff_no_bounded_compl {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hAcom : IsPreconnected Aᶜ) (hBcom : IsPreconnected Bᶜ) :
    IsPreconnected (A ∩ B) ↔ IsEmpty (BoundedPlaneComplementComponent (A ∪ B)) := by
  constructor
  · intro hAB
    obtain ⟨p, hp, hp_unbounded, _⟩ := exists_unbounded_compl_component (hA.union hB)
    refine ⟨fun U => ?_⟩
    obtain ⟨x, hx, hU⟩ := U.val.property
    have hxA : x ∈ Aᶜ := fun h => hx (Or.inl h)
    have hxB : x ∈ Bᶜ := fun h => hx (Or.inr h)
    have hpA : p ∈ Aᶜ := fun h => hp (Or.inl h)
    have hpB : p ∈ Bᶜ := fun h => hp (Or.inr h)
    have hpx := QuantumZipper.CA.Topo.janiszewski hA hB hAB hx hp
      (hAcom.subset_connectedComponentIn hxA Subset.rfl hpA)
      (hBcom.subset_connectedComponentIn hxB Subset.rfl hpB)
    have heq : connectedComponentIn (A ∪ B)ᶜ x = connectedComponentIn (A ∪ B)ᶜ p :=
      (connectedComponentIn_eq hpx)
    apply hp_unbounded
    rw [← heq, ← hU]
    exact U.property
  · intro h
    exact isPreconnected_inter_of_compl_union_preconnected hA hB hAc hBc
      (isPreconnected_compl_of_no_bounded_components (hA.union hB) h)

end LatticeProb.Topology
