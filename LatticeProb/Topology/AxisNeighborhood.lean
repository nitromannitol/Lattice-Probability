/-
Every complement point in a regular axis rectangle has a component accumulating at
every interior axis point. In particular, the complement accumulates along the axis.
-/
import LatticeProb.Topology.LocalFaceIncidence
namespace LatticeProb.PlaneTopology

open Set

variable {X : Type*} [TopologicalSpace X]

/-- The component of each off-trace point in a regular rectangle accumulates at every
interior point of its horizontal axis. -/
theorem axis_mem_closure_component_of_mem_axisBox (S : Set X) (h : X ≃ₜ (ℝ × ℝ))
    (a r : ℝ) (hr : 0 < r)
    (htrace : ∀ z ∈ axisBox a r, h.symm z ∈ S ↔ z.2 = 0)
    (p : X) (hp : p ∉ S) (hpbox : p ∈ h.symm '' axisBox a r)
    (x : ℝ) (hx : x ∈ Ioo (a - r) (a + r)) :
    h.symm (x, 0) ∈ closure (connectedComponentIn Sᶜ p) := by
  obtain ⟨z, hz, rfl⟩ := hpbox
  have hne : z.2 ≠ 0 := fun he => hp ((htrace z hz).mpr he)
  obtain ⟨hpos, hneg⟩ := axis_mem_closure_side_components S h a r hr htrace x hx
  rcases lt_or_gt_of_ne hne with hn | hp'
  · have hm := lower_half_box_subset_component S h a r hr htrace
      ⟨z, ⟨hz.1, hz.2.1, hn⟩, rfl⟩
    rw [← connectedComponentIn_eq hm]
    exact hneg
  · have hm := upper_half_box_subset_component S h a r hr htrace
      ⟨z, ⟨hz.1, hp', hz.2.2⟩, rfl⟩
    rw [← connectedComponentIn_eq hm]
    exact hpos

/-- **Complement accumulation.** The complement of a regular horizontal trace
accumulates at every interior axis point. -/
theorem axis_mem_closure_compl (S : Set X) (h : X ≃ₜ (ℝ × ℝ))
    (a r : ℝ) (hr : 0 < r)
    (htrace : ∀ z ∈ axisBox a r, h.symm z ∈ S ↔ z.2 = 0)
    (x : ℝ) (hx : x ∈ Ioo (a - r) (a + r)) :
    h.symm (x, 0) ∈ closure Sᶜ :=
  closure_mono (connectedComponentIn_subset Sᶜ (h.symm (a, r / 2)))
    (axis_mem_closure_side_components S h a r hr htrace x hx).1

end LatticeProb.PlaneTopology
