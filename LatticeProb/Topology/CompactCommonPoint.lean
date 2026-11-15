import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.Maps.Proper.Basic

/-! # Common points of compact sets -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb.Topology

/-- Membership in a nonempty compact set is closed in the point and the set. -/
theorem isClosed_mem_nonemptyCompacts {X : Type*} [TopologicalSpace X] [T2Space X] :
    IsClosed {p : X × NonemptyCompacts X | p.1 ∈ (p.2 : Set X)} := by
  have heq : {p : X × NonemptyCompacts X | p.1 ∈ (p.2 : Set X)} =
      {p : X × NonemptyCompacts X | ({p.1} : NonemptyCompacts X) ⊔ p.2 = p.2} := by
    ext p
    change p.1 ∈ (p.2 : Set X) ↔ ({p.1} : NonemptyCompacts X) ⊔ p.2 = p.2
    rw [sup_eq_right]
    exact (singleton_subset_iff).symm
  rw [heq]
  exact isClosed_eq ((NonemptyCompacts.continuous_singleton.comp continuous_fst).sup
    continuous_snd) continuous_snd

/-- Two varying nonempty compact sets have a common point in a fixed compact
set on a closed set of pairs. -/
theorem isClosed_exists_mem_inter_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    {F : Set X} (hF : IsCompact F) :
    IsClosed {p : NonemptyCompacts X × NonemptyCompacts X |
      ∃ x ∈ F, x ∈ (p.1 : Set X) ∧ x ∈ (p.2 : Set X)} := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF
  let E : Set ((NonemptyCompacts X × NonemptyCompacts X) × F) :=
    {p | (p.2 : X) ∈ (p.1.1 : Set X) ∧ (p.2 : X) ∈ (p.1.2 : Set X)}
  have hE : IsClosed E := by
    exact (isClosed_mem_nonemptyCompacts.preimage
      (continuous_subtype_val.comp continuous_snd |>.prodMk
        (continuous_fst.comp continuous_fst))).inter
      (isClosed_mem_nonemptyCompacts.preimage
        (continuous_subtype_val.comp continuous_snd |>.prodMk
          (continuous_snd.comp continuous_fst)))
  have heq : {p : NonemptyCompacts X × NonemptyCompacts X |
      ∃ x ∈ F, x ∈ (p.1 : Set X) ∧ x ∈ (p.2 : Set X)} = Prod.fst '' E := by
    ext p
    constructor
    · rintro ⟨x, hxF, hx1, hx2⟩
      exact ⟨(p, ⟨x, hxF⟩), ⟨hx1, hx2⟩, rfl⟩
    · rintro ⟨⟨q, x⟩, hx, rfl⟩
      exact ⟨x, x.property, hx.1, hx.2⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace E hE

end LatticeProb.Topology
