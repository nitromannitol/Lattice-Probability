import LatticeProb.Topology.CompactPlaneComponentCardinality

/-! # Connected complements of compact plane sets -/

open Set Bornology

namespace LatticeProb.Topology

/-- The complement of a compact plane set is preconnected if it has no bounded components. -/
theorem isPreconnected_compl_of_no_bounded_components {K : Set ℂ} (hK : IsCompact K)
    (h : IsEmpty (BoundedPlaneComplementComponent K)) : IsPreconnected Kᶜ := by
  obtain ⟨p, hp, _, hchar⟩ := exists_unbounded_compl_component hK
  have heq : Kᶜ = connectedComponentIn Kᶜ p := by
    apply Subset.antisymm
    · intro x hx
      apply (hchar x hx).2
      intro hb
      exact @isEmptyElim (BoundedPlaneComplementComponent K) h (fun _ => False)
        ⟨⟨connectedComponentIn Kᶜ x, x, hx, rfl⟩, hb⟩
    · exact connectedComponentIn_subset _ _
  rw [heq]
  exact isPreconnected_connectedComponentIn

end LatticeProb.Topology
