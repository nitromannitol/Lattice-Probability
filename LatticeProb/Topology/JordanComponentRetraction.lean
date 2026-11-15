import LatticeProb.Topology.PuncturedPlaneRetraction
import LatticeProb.Topology.SchoenfliesBasedDisc

/-! Retraction onto a Jordan curve from the plane punctured in its bounded component. -/

set_option autoImplicit false

noncomputable section

open Set Metric Bornology
open LQGMetric.JordanMap
open MatedCRTHarmonic.Planar.Schoenflies

namespace LatticeProb

/-- A Jordan curve is a retract of the plane punctured at any point in its bounded component. -/
theorem exists_jordan_component_retraction {Γ : Set ℂ} (hΓ : IsJordanCurve Γ)
    {p : ℂ} (hp : p ∈ Γᶜ) (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    ∃ r : {z : ℂ // z ≠ p} → ℂ, Continuous r ∧
      (∀ x, r x ∈ Γ) ∧
      (∀ x : {z : ℂ // z ≠ p}, (x : ℂ) ∈ Γ → r x = x) := by
  let U := connectedComponentIn Γᶜ p
  have hUo : IsOpen U := (isCompact_of_isJordanCurve hΓ).isClosed.isOpen_compl.connectedComponentIn
  have hpU : p ∈ U := mem_connectedComponentIn hp
  obtain ⟨hfrU, V, hVo, hVc, _, hd, hun, hfrV⟩ := jordan_split hΓ hp hb
  have hV : (closure U)ᶜ = V := by
    ext z
    constructor
    · intro hz
      have hzΓ : z ∉ Γ := by
        intro hzΓ
        apply hz
        exact frontier_subset_closure (hfrU.symm ▸ hzΓ)
      have hzUV : z ∈ U ∪ V := hun ▸ hzΓ
      exact hzUV.resolve_left (fun hzU => hz (subset_closure hzU))
    · intro hz
      have hVsub : V ⊆ Uᶜ := fun _ hzV hzU => hd.ne_of_mem hzU hzV rfl
      have : V ⊆ (closure U)ᶜ := by
        simpa only [interior_compl] using hVo.subset_interior_iff.mpr hVsub
      exact this hz
  have hfr : frontier (closure U) = Γ := by
    rw [← frontier_compl, hV, hfrV]
  have hK : IsCompact (closure U) := hb.isCompact_closure
  have hpi : p ∈ interior (closure U) := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hUo.mem_nhds hpU) subset_closure)
  obtain ⟨e, he, heB, _⟩ := schoenflies_closedDisc_basepoint hΓ hp hb
  obtain ⟨r, hr, hrB, hrfix⟩ := exists_punctured_plane_jordan_retraction hK hpi
    (hV ▸ hVc) (hfr ▸ hΓ) e he (heB.trans hfr.symm)
  exact ⟨r, hr, fun x => hfr ▸ hrB x, fun x hx => hrfix x (hfr.symm ▸ hx)⟩

end LatticeProb
