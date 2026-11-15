import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Brouwer

/-! A topological closed disk does not retract onto its boundary. -/

noncomputable section

open Set Metric
open MatedCRTHarmonic.Planar.Jordan.Brouwer

namespace LatticeProb

/-- A homeomorphic image of the closed disk has no continuous retraction onto
its boundary circle. -/
theorem no_embedded_disk_boundary_retraction {K : Type*} [TopologicalSpace K]
    (e : closedBall (0 : Plane) 1 ≃ₜ K) (r : K → K) (hr : Continuous r)
    (himage : ∀ x, r x ∈ e '' {z | (z : Plane) ∈ sphere 0 1})
    (hfix : ∀ x, x ∈ e '' {z | (z : Plane) ∈ sphere 0 1} → r x = x) : False := by
  let ρ : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1) :=
    ⟨fun x => e.symm (r (e x)), e.symm.continuous.comp (hr.comp e.continuous)⟩
  apply no_retraction ρ
  · intro x
    obtain ⟨y, hy, hye⟩ := himage (e x)
    have : e.symm (r (e x)) = y := by rw [← hye, e.symm_apply_apply]
    simpa [ρ, this] using hy
  · intro x hx
    have h : r (e x) = e x := hfix (e x) ⟨x, hx, rfl⟩
    simp [ρ, h]

end LatticeProb
