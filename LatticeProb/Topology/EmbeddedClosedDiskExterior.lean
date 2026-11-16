import LatticeProb.Topology.EmbeddedDiskJordan

/-! # Exterior of an embedded closed disk -/

noncomputable section

open Set Metric Bornology
open LQGMetric.JordanMap
open MatedCRTHarmonic.Planar.Jordan

namespace LatticeProb

/-- The complement of a planar embedded closed disk is preconnected and unbounded. -/
theorem embedded_closed_disk_compl_preconnected_unbounded {K : Set ℂ}
    (e : closedBall (0 : Plane) 1 ≃ₜ K) :
    IsPreconnected Kᶜ ∧ ¬ IsBounded Kᶜ := by
  let Γ : Set ℂ := Subtype.val '' (e '' {z | (z : Plane) ∈ sphere 0 1})
  have hΓ : IsJordanCurve Γ := isJordanCurve_embedded_disk_boundary e
  obtain ⟨p, hp, q, hq, hb, hu, hdis, hcover, _, _⟩ :=
    jordan_curve_components_complex hΓ
  have hopen := embedded_disk_open_image_eq_component e hΓ rfl hp hb
  have hK : K = Γ ∪ connectedComponentIn Γᶜ p := by
    ext x
    constructor
    · intro hx
      let z := e.symm ⟨x, hx⟩
      have hz : dist (z : Plane) 0 ≤ 1 := z.property
      rcases lt_or_eq_of_le hz with hzlt | hzeq
      · right
        rw [← hopen]
        exact ⟨e z, ⟨z, hzlt, rfl⟩, by simp [z]⟩
      · left
        exact ⟨e z, ⟨z, hzeq, rfl⟩, by simp [z]⟩
    · rintro (hx | hx)
      · obtain ⟨y, _, rfl⟩ := hx
        exact y.property
      · rw [← hopen] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact y.property
  have heq : Kᶜ = connectedComponentIn Γᶜ q := by
    ext x
    constructor
    · intro hx
      have hxΓ : x ∈ Γᶜ := by
        intro hxΓ
        exact hx (hK.symm ▸ Or.inl hxΓ)
      have hxcomp : x ∈ connectedComponentIn Γᶜ p ∪ connectedComponentIn Γᶜ q :=
        hcover ▸ hxΓ
      rcases hxcomp with hxcomp | hxcomp
      · exact False.elim (hx (hK.symm ▸ Or.inr hxcomp))
      · exact hxcomp
    · intro hx hKx
      have hxΓ : x ∈ Γᶜ := connectedComponentIn_subset Γᶜ q hx
      rw [hK] at hKx
      rcases hKx with hKx | hKx
      · exact hxΓ hKx
      · exact (disjoint_left.mp hdis) hKx hx
  rw [heq]
  exact ⟨isPreconnected_connectedComponentIn, hu⟩

/-- The complement of a closed disk embedded from the complex unit disk is
preconnected and unbounded. -/
theorem complex_embedded_closed_disk_compl_preconnected_unbounded {K : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ K) :
    IsPreconnected Kᶜ ∧ ¬ IsBounded Kᶜ := by
  let L := Arcs.complexLIE
  have himage : L.symm.toHomeomorph '' closedBall (0 : Plane) 1 = closedBall (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_closedBall_zero_iff]
      change ‖L.symm w‖ ≤ 1
      rw [L.symm.norm_map]
      exact mem_closedBall_zero_iff.mp hw
    · intro hz
      refine ⟨L z, ?_, by simp⟩
      simpa only [mem_closedBall_zero_iff, L.norm_map] using hz
  exact embedded_closed_disk_compl_preconnected_unbounded
    (((L.symm.toHomeomorph.image _).trans (Homeomorph.setCongr himage)).trans e)

end LatticeProb
