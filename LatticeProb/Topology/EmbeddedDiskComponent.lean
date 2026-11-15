import LatticeProb.Topology.JordanComponentRetraction
import LatticeProb.Topology.EmbeddedDiskNoRetraction

/-! A bounded Jordan component lies in any disk spanning its boundary. -/

set_option autoImplicit false

noncomputable section

open Set Metric Bornology
open LQGMetric.JordanMap
open MatedCRTHarmonic.Planar.Jordan

namespace LatticeProb

/-- The bounded component of the complement of the boundary of an embedded disk
is contained in the disk. -/
theorem bounded_component_subset_embedded_disk {K Γ : Set ℂ}
    (e : closedBall (0 : Plane) 1 ≃ₜ K)
    (hΓ : IsJordanCurve Γ)
    (hboundary : Subtype.val '' (e '' {z | (z : Plane) ∈ sphere 0 1}) = Γ)
    {p : ℂ} (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    connectedComponentIn Γᶜ p ⊆ K := by
  intro q hq
  by_contra hqK
  have hqΓ : q ∈ Γᶜ := connectedComponentIn_subset Γᶜ p hq
  have hqb : IsBounded (connectedComponentIn Γᶜ q) := by
    rw [← connectedComponentIn_eq hq]
    exact hb
  obtain ⟨r, hr, hrmem, hrfix⟩ := exists_jordan_component_retraction hΓ hqΓ hqb
  let j : K → {z : ℂ // z ≠ q} := fun x => ⟨x, fun h => hqK (h ▸ x.property)⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hΓK : Γ ⊆ K := by
    rw [← hboundary]
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  let R : K → K := fun x => ⟨r (j x), hΓK (hrmem (j x))⟩
  have hR : Continuous R := (hr.comp hj).subtype_mk _
  apply no_embedded_disk_boundary_retraction e R hR
  · intro x
    have hmem : r (j x) ∈ Γ := hrmem (j x)
    rw [← hboundary] at hmem
    obtain ⟨y, ⟨z, hz, rfl⟩, heq⟩ := hmem
    exact ⟨z, hz, Subtype.ext heq⟩
  · intro x hx
    apply Subtype.ext
    exact hrfix (j x) (hboundary ▸ ⟨x, hx, rfl⟩)

end LatticeProb
