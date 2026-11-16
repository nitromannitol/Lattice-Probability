import LatticeProb.Topology.CompactPlaneIntersection
import LatticeProb.Topology.EmbeddedClosedDiskExterior

/-! # Contact components of adjacent embedded disks -/

open Set Metric

namespace LatticeProb.Topology

/-- Two embedded disks whose union is an embedded disk meet in at most one component. -/
theorem cardinal_inter_components_le_one_of_embedded_disk_union {A B : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (eAB : closedBall (0 : ℂ) 1 ≃ₜ ↥(A ∪ B)) :
    Cardinal.mk (ConnectedComponents ↥(A ∩ B)) ≤ 1 := by
  have hA := LatticeProb.closure_interior_of_homeomorph_closedDisk eA
  have hB := LatticeProb.closure_interior_of_homeomorph_closedDisk eB
  have hAc : IsConnected A := hA ▸ (LatticeProb.isConnected_interior_of_homeomorph_closedDisk eA).closure
  have hBc : IsConnected B := hB ▸ (LatticeProb.isConnected_interior_of_homeomorph_closedDisk eB).closure
  have hAk : IsCompact A := by
    let : CompactSpace A := eA.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hBk : IsCompact B := by
    let : CompactSpace B := eB.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have h := isPreconnected_inter_of_compl_union_preconnected hAk hBk hAc hBc
    (LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded eAB).1
  let : PreconnectedSpace ↥(A ∩ B) := isPreconnected_iff_preconnectedSpace.mp h
  exact Cardinal.le_one_iff_subsingleton.mpr inferInstance

/-- Adjacent members of a family whose consecutive unions are embedded disks have
at most one intersection component. -/
theorem cardinal_inter_components_le_one_of_adjacent_disks
    (K : ℕ → Set ℂ)
    (hK : ∀ k, Nonempty (closedBall (0 : ℂ) 1 ≃ₜ K k))
    (hsegments : ∀ a b : ℕ, a ≤ b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ ⋃ k ∈ Icc a b, K k))
    (i : ℕ) : Cardinal.mk (ConnectedComponents ↥(K i ∩ K (i + 1))) ≤ 1 := by
  have heq : (⋃ k ∈ Icc i (i + 1), K k) = K i ∪ K (i + 1) := by
    ext x
    simp only [mem_iUnion, mem_Icc, mem_union]
    constructor
    · rintro ⟨k, ⟨hki, hik⟩, hx⟩
      have hk : k = i ∨ k = i + 1 := by omega
      rcases hk with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨i, ⟨le_rfl, by omega⟩, hx⟩
      · exact ⟨i + 1, ⟨by omega, le_rfl⟩, hx⟩
  let e := (hsegments i (i + 1) (by omega)).some
  exact cardinal_inter_components_le_one_of_embedded_disk_union (hK i).some (hK (i + 1)).some
    (e.trans (Homeomorph.setCongr heq))

end LatticeProb.Topology
