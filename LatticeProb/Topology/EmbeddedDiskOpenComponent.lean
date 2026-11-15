import LatticeProb.Topology.EmbeddedDiskComponent

/-! The image of the open disk is the bounded Jordan component. -/

set_option autoImplicit false

noncomputable section

open Set Metric Bornology Topology
open LQGMetric.JordanMap
open MatedCRTHarmonic.Planar.Jordan

namespace LatticeProb

/-- An embedded disk carries its open disk onto the bounded component of the
complement of its boundary. -/
theorem embedded_disk_open_image_eq_component {K Γ : Set ℂ}
    (e : closedBall (0 : Plane) 1 ≃ₜ K)
    (hΓ : IsJordanCurve Γ)
    (hboundary : Subtype.val '' (e '' {z | (z : Plane) ∈ sphere 0 1}) = Γ)
    {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    Subtype.val '' (e '' {z | (z : Plane) ∈ ball 0 1}) =
      connectedComponentIn Γᶜ p := by
  let D : Set (closedBall (0 : Plane) 1) := {z | (z : Plane) ∈ ball 0 1}
  let F : closedBall (0 : Plane) 1 → ℂ := fun z => e z
  have hF : Continuous F := continuous_subtype_val.comp e.continuous
  have hD : IsPreconnected D := by
    rw [← IsInducing.subtypeVal.isPreconnected_image]
    have h : Subtype.val '' D = ball (0 : Plane) 1 := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨⟨x, ball_subset_closedBall hx⟩, hx, rfl⟩
    rw [h]
    exact isPreconnected_ball
  have hav : F '' D ⊆ Γᶜ := by
    rintro y ⟨z, hz, rfl⟩ hy
    rw [← hboundary] at hy
    obtain ⟨w, ⟨v, hv, rfl⟩, hw⟩ := hy
    have heq : z = v := e.injective (Subtype.ext hw.symm)
    subst v
    have hz' : dist (z : Plane) 0 < 1 := hz
    have hv' : dist (z : Plane) 0 = 1 := hv
    linarith
  have hinto : connectedComponentIn Γᶜ p ⊆ F '' D := by
    intro x hx
    have hxK : x ∈ K := bounded_component_subset_embedded_disk e hΓ hboundary hb hx
    let z := e.symm ⟨x, hxK⟩
    have hzclosed : dist (z : Plane) 0 ≤ 1 := z.property
    have hznot : dist (z : Plane) 0 ≠ 1 := by
      intro hz
      have hxΓ : x ∈ Γ := by
        rw [← hboundary]
        exact ⟨e z, ⟨z, hz, rfl⟩, by simp [z]⟩
      exact (connectedComponentIn_subset Γᶜ p hx) hxΓ
    refine ⟨z, lt_of_le_of_ne hzclosed hznot, ?_⟩
    simp [F, z]
  have hpD : p ∈ F '' D := hinto (mem_connectedComponentIn hp)
  have hout : F '' D ⊆ connectedComponentIn Γᶜ p :=
    (hD.image F hF.continuousOn).subset_connectedComponentIn hpD hav
  simpa only [F, D, image_image, Function.comp_def] using hout.antisymm hinto

end LatticeProb
