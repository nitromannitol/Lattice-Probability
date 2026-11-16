import LatticeProb.Topology.ConsecutiveDisksContactComponents
import LatticeProb.Topology.EmbeddedDiskComponentBound
import LatticeProb.Topology.CompactPlaneIntersection

/-! # Intersection components of consecutive planar disks -/

open Set Metric Bornology

namespace LatticeProb

/-- Nonadjacent disks in a consecutive family meet in at most two components. -/
theorem cardinal_inter_components_le_two_of_consecutive_disks
    (K : ℕ → Set ℂ)
    (hK : ∀ k, Nonempty (closedBall (0 : ℂ) 1 ≃ₜ K k))
    (hsegments : ∀ a b : ℕ, a ≤ b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ ⋃ k ∈ Icc a b, K k))
    (hdis : ∀ a b, a ≠ b → Disjoint (interior (K a)) (interior (K b)))
    {i j : ℕ} (hij : i + 1 < j) :
    Cardinal.mk (ConnectedComponents ↥(K i ∩ K j)) ≤ 2 := by
  let : Subsingleton (Topology.BoundedPlaneComplementComponent (K i ∪ K j)) := ⟨by
    intro U V
    obtain ⟨p, hp, hU⟩ := U.val.property
    obtain ⟨q, hq, hV⟩ := V.val.property
    apply Subtype.ext
    apply Subtype.ext
    rw [hU, hV]
    exact bounded_complement_components_eq_of_consecutive_disks K hK hsegments hdis hij hp hq
      (hU ▸ U.property) (hV ▸ V.property)⟩
  exact Topology.cardinal_inter_components_le_two_of_embedded_disks
    (hK i).some (hK j).some (hdis i j (by omega))

/-- Adjacent disks in a consecutive family meet in at most one component. -/
theorem cardinal_inter_components_le_one_of_consecutive_disks
    (K : ℕ → Set ℂ)
    (hK : ∀ k, Nonempty (closedBall (0 : ℂ) 1 ≃ₜ K k))
    (hsegments : ∀ a b : ℕ, a ≤ b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ ⋃ k ∈ Icc a b, K k))
    (i : ℕ) : Cardinal.mk (ConnectedComponents ↥(K i ∩ K (i + 1))) ≤ 1 := by
  have hseg : (⋃ k ∈ Icc i (i + 1), K k) = K i ∪ K (i + 1) := by
    ext x
    simp only [mem_iUnion, mem_Icc, mem_union]
    constructor
    · rintro ⟨k, ⟨hki, hkj⟩, hx⟩
      have : k = i ∨ k = i + 1 := by omega
      rcases this with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨i, ⟨le_rfl, by omega⟩, hx⟩
      · exact ⟨i + 1, ⟨by omega, le_rfl⟩, hx⟩
  let e : closedBall (0 : ℂ) 1 ≃ₜ ↥(K i ∪ K (i + 1)) :=
    (hsegments i (i + 1) (by omega)).some.trans (Homeomorph.setCongr hseg)
  have hcom := (complex_embedded_closed_disk_compl_preconnected_unbounded e).1
  have hcompact (k : ℕ) : IsCompact (K k) := by
    let : CompactSpace (K k) := (hK k).some.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hconnected (k : ℕ) : IsConnected (K k) := by
    have h := closure_interior_of_homeomorph_closedDisk (hK k).some
    exact h ▸ (isConnected_interior_of_homeomorph_closedDisk (hK k).some).closure
  have hinter := Topology.isPreconnected_inter_of_compl_union_preconnected
    (hcompact i) (hcompact (i + 1)) (hconnected i) (hconnected (i + 1)) hcom
  let : PreconnectedSpace ↥(K i ∩ K (i + 1)) := isPreconnected_iff_preconnectedSpace.mp hinter
  exact Cardinal.le_one_iff_subsingleton.mpr inferInstance

end LatticeProb
