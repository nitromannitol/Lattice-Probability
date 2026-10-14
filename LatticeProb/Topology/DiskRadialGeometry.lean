/-
# Radial segments in the coordinate disk

Every point of an inward radial segment other than its original circle endpoint
lies in the open coordinate disk.
-/
import LatticeProb.Topology.DiskEndpointNeighborhoods
import LatticeProb.Topology.DiskPolygonalApproximation



open Set

namespace LatticeProb.Topology

/-- A radial segment enters the open disk immediately after its circle endpoint. -/
theorem mem_open_disk_of_mem_radial_segment_of_ne {a w : ℝ × ℝ}
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hw : w ∈ segment ℝ a (ρ • a)) (hne : w ≠ a) :
    w.1 ^ 2 + w.2 ^ 2 < 1 := by
  obtain ⟨t, ⟨hρt, ht⟩, rfl⟩ := (mem_segment_self_smul_iff a hρ1.le).mp hw
  have ht1 : t < 1 := lt_of_le_of_ne ht (by
    intro heq
    apply hne
    rw [heq, one_smul])
  exact smul_mem_open_unit_disk ha.le (hρ0.trans hρt) ht1

/-- **Strict radial disk interior.** The whole inward radial segment, including its original endpoint, stays in the disk. -/
theorem segment_self_smul_subset_coordinate_disk {a : ℝ × ℝ}
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    segment ℝ a (ρ • a) ⊆ {w | w.1 ^ 2 + w.2 ^ 2 ≤ 1} := by
  intro w hw
  by_cases hwa : w = a
  · exact hwa ▸ ha.le
  · exact (mem_open_disk_of_mem_radial_segment_of_ne ha hρ0 hρ1 hw hwa).le

end LatticeProb.Topology
