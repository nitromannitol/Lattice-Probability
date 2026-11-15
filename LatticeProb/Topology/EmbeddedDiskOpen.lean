import LatticeProb.Topology.EmbeddedDiskOpenComponent

/-! Openness of the image of an embedded disk. -/

set_option autoImplicit false

noncomputable section

open Set Metric Bornology Topology
open LQGMetric.JordanMap
open MatedCRTHarmonic.Planar.Jordan
open MatedCRTHarmonic.Planar.Schoenflies

namespace LatticeProb

/-- An embedded open disk with Jordan boundary has open image. -/
theorem isOpen_embedded_disk_open_image {K Γ : Set ℂ}
    (e : closedBall (0 : Plane) 1 ≃ₜ K)
    (hΓ : IsJordanCurve Γ)
    (hboundary : Subtype.val '' (e '' {z | (z : Plane) ∈ sphere 0 1}) = Γ) :
    IsOpen (Subtype.val '' (e '' {z | (z : Plane) ∈ ball 0 1})) := by
  obtain ⟨p, hp, _, _, hb, _⟩ := jordan_curve_components_complex hΓ
  rw [embedded_disk_open_image_eq_component e hΓ hboundary hp hb]
  exact (isCompact_of_isJordanCurve hΓ).isClosed.isOpen_compl.connectedComponentIn

end LatticeProb
